/-
Design tokens. Every visual decision of the SVG backend lives here;
`P10t.Render` has no literal colors, sizes or gaps.
-/

namespace P10t

/-- Look and feel; lengths in px. -/
structure Theme where
  -- ### Surface & ink
  surface      : String := "none"      -- chart surface ("none" = transparent)
  pagePlane    : String := "none"      -- behind several charts (gallery)
  inkPrimary   : String := "#171717"   -- title, watermark      (gray-1000)
  inkSecondary : String := "#666666"   -- subtitle, legend, axis titles (gray-900)
  inkMuted     : String := "#8f8f8f"   -- tick labels           (gray-700)
  grid         : String := "#ebebeb"   -- hairline gridlines    (gray-200)
  /-- Vertical gridlines at the X ticks, in addition to horizontal ones. -/
  gridVertical : Bool := true
  /-- Target number of intervals between ticks on each axis. -/
  xTicksTarget : Nat := 6
  yTicksTarget : Nat := 5
  /-- Minimum clear space between neighbouring X tick labels (px). -/
  xLabelGap    : Float := 8
  axis         : String := "#c9c9c9"   -- axis lines + arrowheads (gray-500)

  -- ### Series colors, fixed slot order (CVD-validated); past the last slot: fallback
  series : Array String :=
    #["#0070f3", "#e8890c", "#12a594", "#8e4ec6",
      "#ea3e83", "#297a3a", "#ee0000", "#0ca7d0"]
  seriesFallback : String := "#8f8f8f"

  -- ### Typography
  fontFamily    : String :=
    "Geist, 'Geist Sans', Inter, system-ui, -apple-system, 'Segoe UI', sans-serif"
  tickFontFamily : String :=
    "'Geist Mono', ui-monospace, 'SF Mono', Menlo, Consolas, monospace"
  titleSize     : Float := 14
  titleWeight   : String := "600"
  subtitleSize  : Float := 13
  legendSize    : Float := 13
  axisTitleSize : Float := 12
  tickSize      : Float := 11
  glyphEm       : Float := 0.62   -- mean glyph advance (em), for width estimates

  -- ### Marks
  lineWidth  : Float := 2
  legendDotR : Float := 4
  axisOvershoot : Float := 10       -- axes extend past the plot so arrowheads clear the data
  legendDotAlign : Float := 0.28    -- dot centre above baseline, fraction of legendSize
  arrowheads : Bool := true

  -- ### Spacing
  padOuter     : Float := 8    -- canvas edge → first element
  padRight     : Float := 16   -- room for the X arrowhead / last tick label
  rowGap       : Float := 8    -- between header rows
  headerToPlot : Float := 12   -- last header row → axis arrow tip
  yTickGap     : Float := 12   -- axis → right edge of Y tick labels
  xTickGap     : Float := 20   -- axis → baseline of X tick labels
  axisTitleGap : Float := 12   -- tick labels → axis title

  -- ### Watermark (centered in the plot, behind the data)
  watermarkSize    : Float := 40
  watermarkWeight  : String := "700"
  watermarkSpacing : Float := 6     -- letter-spacing
  watermarkOpacity : Float := 0.06
  deriving Repr

/-- How the X axis writes its tick values. -/
inductive AxisFormat where
  /-- plain decimal -/
  | number
  /-- Unix milliseconds, shown as UTC dates/times -/
  | epochMs
  /-- Unix seconds, shown as UTC dates/times -/
  | epochSeconds
  deriving Repr, DecidableEq

/-- Per-chart text and options; absent fields take no space. -/
structure ChartSpec where
  title     : Option String := none
  subtitle  : Option String := none
  xTitle    : Option String := none
  yTitle    : Option String := none
  watermark : Option String := none
  xFormat   : AxisFormat := .number
  yDecimals : Option Nat := none   -- fixed Y decimals with thousands grouping; none = shortest
  lastValue : Bool := false        -- dotted guide + value at the Y axis for each last sample
  deriving Repr

end P10t
