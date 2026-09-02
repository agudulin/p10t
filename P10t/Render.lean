/-
# p10t — SVG backend (unverified)

The rasterization layer from the architecture: it consumes *already
verified* rational coordinates from `P10t.Basic` and emits an SVG
string. The browser does the actual rasterization.

Layout: the verified core maps data into the *plot rectangle*
`[0, width] × [0, height]` (Y grows upward). This backend places that
rectangle inside the canvas with margins, translating by
`(layout.left, layout.top)` and flipping Y for SVG. The margins are a
function of the viewport, the chart spec and the theme only — so for
any given chart they are constants, and a constant translation plus a
reflection cannot break monotonicity, exact proportionality, or range
bounds.

Everything textual (title, subtitle, legend, tick labels, axis titles)
is drawn *outside* the plot rectangle, separated from it by the gaps in
`Theme`; since the verified core guarantees every data point lands
inside the rectangle, text and data can never collide. The only thing
inside the rectangle besides data is the optional watermark, drawn
behind it.

No colors, sizes, or gaps appear in this file: see `P10t.Theme`.
-/
import P10t.Basic
import P10t.Time
import P10t.Ticks
import P10t.Theme

namespace P10t

/-- The backend boundary: exact rational → display float. -/
def toF (r : ℚ) : Float :=
  r.num.toFloat / r.den.toFloat

/-- Trim fixed-point `Float.toString` output ("320.000000" → "320")
so the emitted SVG stays readable. -/
def fmt (x : Float) : String :=
  let s := x.toString
  if s.contains "." then
    let s := toString <| s.dropEndWhile '0' |>.dropEndWhile '.'
    if s.isEmpty || s == "-" then "0" else s
  else s

/-- Escape text for use in SVG element content / attributes. -/
private def esc (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ match c with
      | '&' => "&amp;" | '<' => "&lt;" | '>' => "&gt;" | '"' => "&quot;"
      | c => c.toString) ""

/-- Estimated rendered width of `s` at `size` px (see `Theme.glyphEm`). -/
private def textW (th : Theme) (size : Float) (s : String) : Float :=
  th.glyphEm * size * s.length.toFloat

/-! ## Label formatting -/

/-- Insert thousands separators into a string of digits. -/
private def groupThousands (digits : String) : String :=
  let cs := digits.toList.reverse
  let rec go : List Char → Nat → List Char
    | [], _ => []
    | c :: cs, n => (if n > 0 && n % 3 == 0 then [',', c] else [c]) ++ go cs (n + 1)
  String.ofList (go cs 0).reverse

/-- `x` with exactly `d` decimals (trailing zeros trimmed) and grouped
thousands: `76374.757921` → `76,374.76` at `d = 2`. -/
def fmtFixed (x : Float) (d : Nat) : String :=
  let m := (10 : Float) ^ d.toFloat
  let r := (x * m).round / m
  let s := fmt r
  let neg := s.startsWith "-"
  let s := if neg then (s.drop 1).toString else s
  let (ip, fp) := match s.splitOn "." with
    | [i, f] => (i, "." ++ f)
    | _ => (s, "")
  (if neg then "-" else "") ++ groupThousands ip ++ fp

/-- Y ticks: exact values with labels. Decimals come from the spec, or
else from the tick step. Falls back to the window edges if no
round-number tick fits. -/
def yTicks (spec : ChartSpec) (th : Theme) (vp : Viewport) : Array (ℚ × String) :=
  let (vals, d) := Ticks.numeric vp.vMin vp.vMax th.yTicksTarget
  let d := spec.yDecimals.getD d
  let vals := if vals.size ≥ 2 then vals else #[vp.vMin, vp.vMax]
  vals.map fun v => (v, fmtFixed (toF v) d)

/-- The Y label format the ticks use, for the last-value marker. -/
def yLabel (spec : ChartSpec) (th : Theme) (vp : Viewport) (v : ℚ) : String :=
  let (_, d) := Ticks.numeric vp.vMin vp.vMax th.yTicksTarget
  fmtFixed (toF v) (spec.yDecimals.getD d)

/-- Large round numbers with a suffix: `2000000000` → `2B`. Only when
every value stays exact with at most one decimal at that scale, so
`1700000500000` keeps its digits rather than becoming a vague `1.7T`. -/
def fmtCompact (vals : Array ℚ) (d : Nat) : Array String :=
  let plain := vals.map fun v => fmtFixed (toF v) d
  let big := vals.foldl (fun m v => max m |v|) 0
  let scales : List (ℚ × String) := [(10 ^ 12, "T"), (10 ^ 9, "B"), (10 ^ 6, "M")]
  match scales.find? (fun (u, _) => big ≥ u) with
  | none => plain
  | some (u, sfx) =>
    if vals.all (fun v => (v / u * 10).den == 1) then
      vals.map fun v => if v == 0 then "0" else fmtFixed (toF (v / u)) 1 ++ sfx
    else plain

/-- Drop labels until neighbours no longer overlap: keep every `k`-th,
smallest `k` that fits. Tick values stay, so gridlines are unchanged. -/
def thinLabels (th : Theme) (vp : Viewport) (ticks : Array (ℚ × String)) :
    Array (ℚ × String) :=
  let pos := ticks.map fun (t, l) => (toF (vp.mapX t), textW th th.tickSize l)
  let fits (k : Nat) : Bool :=
    (List.range ticks.size).all fun i =>
      i + k ≥ ticks.size || i % k != 0 ||
      (let (xa, wa) := pos[i]!
       let (xb, wb) := pos[i + k]!
       xb - xa ≥ (wa + wb) / 2 + th.xLabelGap)
  let k := ((List.range ticks.size).map (· + 1)).find? fits |>.getD ticks.size
  ticks.mapIdx fun i (t, l) => (t, if i % k == 0 then l else "")

/-- X ticks: round numbers, or calendar-aligned UTC instants for epoch axes. -/
def xTicks (spec : ChartSpec) (th : Theme) (vp : Viewport) : Array (ℚ × String) :=
  let ticks := match spec.xFormat with
    | .number =>
      let (vals, d) := Ticks.numeric vp.tMin vp.tMax th.xTicksTarget
      vals.zip (fmtCompact vals d)
    | .epochMs => Ticks.epoch vp.tMin vp.tMax 1 th.xTicksTarget
    | .epochSeconds => Ticks.epoch vp.tMin vp.tMax 1000 th.xTicksTarget
  let ticks := if ticks.size ≥ 2 then ticks
    else #[(vp.tMin, fmt (toF vp.tMin)), (vp.tMax, fmt (toF vp.tMax))]
  thinLabels th vp ticks

/-! ## Layout: margins derived from content -/

/-- Pack legend items into rows no wider than `maxW`: each item is
`(series index, name, x offset within its row)`. Always at least one
item per row, so an over-long name overflows rather than vanishes. -/
private def legendRows (th : Theme) (maxW : Float) (names : Array String) :
    Array (Array (Nat × String × Float)) :=
  let gap := 2 * th.legendDotR + 8   -- dot → label
  let sep : Float := 18              -- label → next dot
  let items := names.mapIdx fun i n => (i, n)
  let (rows, cur, _) := items.foldl (fun (rows, cur, x) (i, n) =>
    let w := gap + textW th th.legendSize n
    if x > 0 && x + w > maxW then
      (rows.push cur, #[(i, n, (0 : Float))], w + sep)
    else
      (rows, cur.push (i, n, x), x + w + sep))
    ((#[] : Array (Array (Nat × String × Float))),
     (#[] : Array (Nat × String × Float)), (0 : Float))
  if cur.isEmpty then rows else rows.push cur

/-- Canvas-space frame around the plot rectangle. -/
structure Layout where
  left   : Float
  top    : Float
  right  : Float
  bottom : Float
  /-- Baselines of the header rows (title, subtitle), if present. -/
  titleY    : Option Float
  subtitleY : Option Float
  /-- Legend rows (baseline, items); empty for fewer than two series. -/
  legend    : Array (Float × Array (Nat × String × Float))

def layout (vp : Viewport) (spec : ChartSpec) (th : Theme) (names : Array String)
    (leftLabels : Array String := #[]) : Layout :=
  -- header rows, top to bottom
  let y := th.padOuter
  let (titleY, y) := match spec.title with
    | some _ => (some (y + th.titleSize), y + th.titleSize + th.rowGap)
    | none => (none, y)
  let (subtitleY, y) := match spec.subtitle with
    | some _ => (some (y + th.subtitleSize), y + th.subtitleSize + th.rowGap)
    | none => (none, y)
  -- a legend only for ≥ 2 series (one series is named by the title),
  -- wrapped to the plot width
  let rows := if names.size ≥ 2 then legendRows th (toF vp.width) names else #[]
  let (legend, y) := rows.foldl (fun (acc, y) row =>
    (acc.push (y + th.legendSize, row), y + th.legendSize + th.rowGap))
    ((#[] : Array (Float × Array (Nat × String × Float))), y)
  let top := y + th.headerToPlot + th.axisOvershoot
  -- left: [pad][Y axis title][widest tick label][gap] axis
  let widest := ((yTicks spec th vp).map (·.2.length) ++ leftLabels.map (·.length)).foldl
    max 0
  let labelW := th.glyphEm * th.tickSize * widest.toFloat
  let yTitleW := if spec.yTitle.isSome then th.axisTitleSize + th.axisTitleGap else 0
  let left := th.padOuter + yTitleW + labelW + th.yTickGap
  -- bottom: axis [gap][tick labels][gap][X axis title][pad]
  let xTitleH := if spec.xTitle.isSome then th.axisTitleGap + th.axisTitleSize else 0
  let bottom := th.xTickGap + xTitleH + th.padOuter
  { left, top, right := max th.padRight (th.axisOvershoot + th.padOuter), bottom,
    titleY, subtitleY, legend }

/-- Map a data point to canvas coordinates: verified plot-rectangle
position, plus the constant margin offset, Y flipped for SVG. -/
def Viewport.mapScreen (vp : Viewport) (L : Layout) (t v : ℚ) : Float × Float :=
  (toF (vp.mapX t) + L.left, toF (vp.height - vp.mapY v) + L.top)

/-- Total canvas size for a plot rectangle of `w × h`. -/
def canvasSize (vp : Viewport) (L : Layout) : Float × Float :=
  (L.left + toF vp.width + L.right, L.top + toF vp.height + L.bottom)

/-! ## Elements -/

private def seriesColor (th : Theme) (i : Nat) : String :=
  th.series.getD i th.seriesFallback

private def text (x y : Float) (size : Float) (fill : String) (s : String)
    (extra : String := "") : String :=
  s!"<text x=\"{fmt x}\" y=\"{fmt y}\" font-size=\"{fmt size}\" " ++
  s!"fill=\"{fill}\" {extra}>{esc s}</text>"

private def polyline (th : Theme) (col : String) (vp : Viewport) (L : Layout)
    (pts : Array (ℚ × ℚ)) : String :=
  let s :=
    pts.foldl (fun acc (t, v) =>
      let (x, y) := vp.mapScreen L t v
      acc ++ s!"{fmt x},{fmt y} ") ""
  s!"<polyline fill=\"none\" stroke=\"{col}\" stroke-width=\"{fmt th.lineWidth}\" " ++
  s!"stroke-linejoin=\"round\" stroke-linecap=\"round\" points=\"{s}\"/>"

/-- Title and subtitle, aligned with the plot's left edge. -/
private def headerSvg (spec : ChartSpec) (th : Theme) (L : Layout) : String :=
  let t := match spec.title, L.titleY with
    | some s, some y =>
      text L.left y th.titleSize th.inkPrimary s s!"font-weight=\"{th.titleWeight}\""
    | _, _ => ""
  let st := match spec.subtitle, L.subtitleY with
    | some s, some y => text L.left y th.subtitleSize th.inkSecondary s
    | _, _ => ""
  t ++ " " ++ st

/-- Legend rows: a colored dot beside each series name, text in ink. -/
private def legendSvg (th : Theme) (L : Layout) : String :=
  let r := th.legendDotR
  let gap := 2 * r + 8
  L.legend.foldl (fun acc (y, row) =>
    row.foldl (fun acc (i, name, dx) =>
      let x := L.left + dx
      acc ++
      s!"<circle cx=\"{fmt (x + r)}\" cy=\"{fmt (y - th.legendSize * th.legendDotAlign)}\" " ++
      s!"r=\"{fmt r}\" fill=\"{seriesColor th i}\"/> " ++
      text (x + gap) y th.legendSize th.inkSecondary name ++ " ") acc) ""

/-- Watermark: centered in the plot rectangle, drawn before the data. -/
private def watermarkSvg (spec : ChartSpec) (th : Theme) (vp : Viewport)
    (L : Layout) : String :=
  match spec.watermark with
  | none => ""
  | some s =>
    let cx := L.left + toF vp.width / 2
    let cy := L.top + toF vp.height / 2 + th.watermarkSize * 0.35
    text cx cy th.watermarkSize th.inkPrimary s <|
      s!"text-anchor=\"middle\" font-weight=\"{th.watermarkWeight}\" " ++
      s!"letter-spacing=\"{fmt th.watermarkSpacing}\" " ++
      s!"fill-opacity=\"{fmt th.watermarkOpacity}\" pointer-events=\"none\""

/-- Gridlines, axes (with optional arrowheads), tick labels and axis
titles. Tick positions come from the verified `mapX`/`mapY`, so labels
sit exactly at the values they name. -/
private def axesSvg (spec : ChartSpec) (th : Theme) (vp : Viewport) (L : Layout)
    (occupiedY : Array Float := #[]) : String :=
  let x0 := L.left                  -- Y axis
  let y0 := L.top + toF vp.height   -- X axis
  let x1 := L.left + toF vp.width   -- right edge (arrow tip →)
  let y1 := L.top                   -- top edge (arrow tip ↑)
  let yOf (v : ℚ) : Float := L.top + toF (vp.height - vp.mapY v)
  let xOf (t : ℚ) : Float := L.left + toF (vp.mapX t)
  let yT := yTicks spec th vp
  let xT := xTicks spec th vp
  let tick (x y : Float) (s anchor : String) : String :=
    text x y th.tickSize th.inkMuted s <|
      s!"text-anchor=\"{anchor}\" font-family=\"{th.tickFontFamily}\" " ++
      "style=\"font-variant-numeric:tabular-nums\""
  -- a Y tick label yields to a last-value label sitting on top of it
  let yTick (y : Float) (s : String) : String :=
    if occupiedY.any (fun o => Float.abs (o - y) < th.tickSize) then ""
    else tick (x0 - th.yTickGap) (y + 4) s "end"
  let hline (y : Float) (col : String) : String :=
    s!"<line x1=\"{fmt x0}\" y1=\"{fmt y}\" x2=\"{fmt x1}\" y2=\"{fmt y}\" " ++
    s!"stroke=\"{col}\" stroke-width=\"1\"/>"
  let vline (x : Float) (col : String) : String :=
    s!"<line x1=\"{fmt x}\" y1=\"{fmt y0}\" x2=\"{fmt x}\" y2=\"{fmt y1}\" " ++
    s!"stroke=\"{col}\" stroke-width=\"1\"/>"
  -- axes overshoot the plot rectangle so the arrow tips sit past the data
  let yTip := y1 - th.axisOvershoot
  let xTip := x1 + th.axisOvershoot
  let arrows :=
    if th.arrowheads then
      s!"<polygon points=\"{fmt (x0 - 3.5)},{fmt (yTip + 7)} " ++
      s!"{fmt (x0 + 3.5)},{fmt (yTip + 7)} {fmt x0},{fmt yTip}\" fill=\"{th.axis}\"/> " ++
      s!"<polygon points=\"{fmt (xTip - 7)},{fmt (y0 - 3.5)} " ++
      s!"{fmt (xTip - 7)},{fmt (y0 + 3.5)} {fmt xTip},{fmt y0}\" fill=\"{th.axis}\"/> "
    else ""
  let xTitle := match spec.xTitle with
    | some s =>
      text ((x0 + x1) / 2) (y0 + th.xTickGap + th.axisTitleGap + th.axisTitleSize)
        th.axisTitleSize th.inkSecondary s "text-anchor=\"middle\""
    | none => ""
  let yTitle := match spec.yTitle with
    | some s =>
      let tx := th.padOuter + th.axisTitleSize
      let ty := (y0 + y1) / 2
      s!"<text transform=\"translate({fmt tx},{fmt ty}) rotate(-90)\" " ++
      s!"font-size=\"{fmt th.axisTitleSize}\" fill=\"{th.inkSecondary}\" " ++
      s!"text-anchor=\"middle\">{esc s}</text>"
    | none => ""
  -- gridlines at every tick; the axis lines cover the ones on the edges
  (yT.foldl (fun acc (v, _) =>
    let y := yOf v
    if Float.abs (y - y0) < 0.5 then acc else acc ++ hline y th.grid ++ " ") "") ++
  (if th.gridVertical then
    xT.foldl (fun acc (t, _) =>
      let x := xOf t
      if Float.abs (x - x0) < 0.5 then acc else acc ++ vline x th.grid ++ " ") ""
   else "") ++
  -- axes
  s!"<line x1=\"{fmt x0}\" y1=\"{fmt y0}\" x2=\"{fmt x0}\" y2=\"{fmt yTip}\" " ++
  s!"stroke=\"{th.axis}\" stroke-width=\"1\"/> " ++
  s!"<line x1=\"{fmt x0}\" y1=\"{fmt y0}\" x2=\"{fmt xTip}\" y2=\"{fmt y0}\" " ++
  s!"stroke=\"{th.axis}\" stroke-width=\"1\"/> " ++ arrows ++
  -- Y tick labels: right-aligned, `yTickGap` left of the axis
  (yT.foldl (fun acc (v, l) => acc ++ yTick (yOf v) l ++ " ") "") ++
  -- X tick labels: `xTickGap` below the axis, centered on the tick
  (xT.foldl (fun acc (t, l) =>
    if l.isEmpty then acc else
    acc ++ tick (xOf t) (y0 + th.xTickGap) l "middle" ++ " ") "") ++
  xTitle ++ " " ++ yTitle

/-- Last-value markers: for each series whose last sample is inside the
window, a dotted guide from the sample to the Y axis, a dot on the
sample, and the value written at the axis in the series color. The
guide's y comes from the verified `mapY`, so it sits exactly at the
value it names. -/
private def lastValueSvg (spec : ChartSpec) (th : Theme) (vp : Viewport)
    (L : Layout) (series : Array (String × Array (ℚ × ℚ))) : String :=
  if !spec.lastValue then "" else
  let x0 := L.left
  let items := series.mapIdx fun i ((_, pts) : String × Array (ℚ × ℚ)) =>
    match pts.back? with
    | some (t, v) =>
      if vp.inWindow t v then
        let (x, y) := vp.mapScreen L t v
        let col := seriesColor th i
        s!"<line x1=\"{fmt x0}\" y1=\"{fmt y}\" x2=\"{fmt x}\" y2=\"{fmt y}\" " ++
        s!"stroke=\"{col}\" stroke-width=\"1\" stroke-dasharray=\"2 3\" " ++
        s!"stroke-opacity=\"0.8\"/> " ++
        s!"<circle cx=\"{fmt x}\" cy=\"{fmt y}\" r=\"3\" fill=\"{col}\"/> " ++
        text (x0 - th.yTickGap) (y + 4) th.tickSize col (yLabel spec th vp v)
          (s!"text-anchor=\"end\" font-family=\"{th.tickFontFamily}\" font-weight=\"600\" " ++
           s!"paint-order=\"stroke\" stroke=\"{th.surface}\" stroke-width=\"3\" " ++
           "style=\"font-variant-numeric:tabular-nums\"") ++ " "
      else ""
    | none => ""
  String.join items.toList

/-- Canvas y of each last-value label, so tick labels can yield to them. -/
private def lastValueYs (spec : ChartSpec) (vp : Viewport) (L : Layout)
    (series : Array (String × Array (ℚ × ℚ))) : Array Float :=
  if !spec.lastValue then #[] else
  series.filterMap fun ((_, pts) : String × Array (ℚ × ℚ)) =>
    match pts.back? with
    | some (t, v) => if vp.inWindow t v then some (vp.mapScreen L t v).2 else none
    | none => none

/-- Labels the last-value markers will put left of the axis, so the
layout can reserve room for them. -/
private def lastValueLabels (spec : ChartSpec) (th : Theme) (vp : Viewport)
    (series : Array (String × Array (ℚ × ℚ))) : Array String :=
  if !spec.lastValue then #[] else
  series.filterMap fun ((_, pts) : String × Array (ℚ × ℚ)) =>
    match pts.back? with
    | some (t, v) => if vp.inWindow t v then some (yLabel spec th vp v) else none
    | none => none

/-- Render a full SVG document: verified layout in, text out.
`spec` and `theme` default to "no chrome" and the house style. -/
def renderSVG (vp : Viewport) (series : Array (String × Array (ℚ × ℚ)))
    (spec : ChartSpec := {}) (theme : Theme := {}) : String :=
  let L := layout vp spec theme (series.map (·.1)) (lastValueLabels spec theme vp series)
  let (cw, ch) := canvasSize vp L
  let w := fmt cw
  let h := fmt ch
  let data : String :=
    " ".intercalate (series.mapIdx fun i (_, pts) =>
      polyline theme (seriesColor theme i) vp L pts).toList
  let docTitle := match spec.title with
    | some t => s!"<title>{esc t}</title> "
    | none => ""
  -- Clip every series to the plot rectangle so points outside the window
  -- (zoomed views) never draw over margins or labels. The id encodes the
  -- rectangle, so nested documents with different geometry don't collide.
  let pw := fmt (toF vp.width)
  let ph := fmt (toF vp.height)
  let clipId := s!"plot-{fmt L.left}-{fmt L.top}-{pw}-{ph}"
  let clip :=
    s!"<clipPath id=\"{clipId}\"><rect x=\"{fmt L.left}\" y=\"{fmt L.top}\" " ++
    s!"width=\"{pw}\" height=\"{ph}\"/></clipPath> "
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {w} {h}\" " ++
  s!"width=\"{w}\" height=\"{h}\" font-family=\"{theme.fontFamily}\"> " ++
  docTitle ++
  (if theme.surface == "none" then "" else
    s!"<rect x=\"0\" y=\"0\" width=\"{w}\" height=\"{h}\" fill=\"{theme.surface}\"/> ") ++
  headerSvg spec theme L ++ " " ++
  legendSvg theme L ++ " " ++
  watermarkSvg spec theme vp L ++ " " ++
  axesSvg spec theme vp L (lastValueYs spec vp L series) ++ " " ++
  clip ++ s!"<g clip-path=\"url(#{clipId})\">" ++ data ++ "</g> " ++
  lastValueSvg spec theme vp L series ++ "</svg>"

/-- `renderSVG` plus the canvas size, for composers that nest documents. -/
def renderSized (vp : Viewport) (series : Array (String × Array (ℚ × ℚ)))
    (spec : ChartSpec := {}) (theme : Theme := {}) : String × Float × Float :=
  let L := layout vp spec theme (series.map (·.1)) (lastValueLabels spec theme vp series)
  let (w, h) := canvasSize vp L
  (renderSVG vp series spec theme, w, h)

end P10t
