/-
# p10t — `render` command

    p10t render [options] < data.json > chart.svg

Reads a JSON document, selects one or more series from it, and draws
them through the verified layout. The data never passes through a
float: JSON digits become rationals (`P10t.Json`), the contract
checker runs on those rationals, and only the final, already-verified
screen coordinates are converted for the SVG text.

Exit codes tell the caller *why* nothing was drawn:

    0  chart written
    1  usage error
    2  input is not JSON, path not found, or values not numeric
    3  data contract violated: timestamps not strictly increasing, or empty
    4  no valid window: degenerate data or bad --window

A one-line JSON report goes to stderr: what was parsed, which checks
passed, and the exact window, so a caller can log it as a certificate.
-/
import P10t.Json
import P10t.Demos

namespace P10t.Cli

open P10t.Json

structure Opts where
  input : Option String := none
  output : Option String := none
  paths : Array String := #[]
  names : Array String := #[]
  tKey : String := "0"
  vKey : String := "1"
  width : ℚ := 640
  height : ℚ := 360
  /-- vertical padding as a fraction of the value range -/
  pad : ℚ := 1 / 20
  window : Option (ℚ × ℚ × ℚ × ℚ) := none
  title : Option String := none
  subtitle : Option String := none
  xTitle : Option String := none
  yTitle : Option String := none
  xFormat : AxisFormat := .number
  yDecimals : Option ℕ := none
  lastValue : Bool := false
  quiet : Bool := false

def usage : String := "
usage: p10t render [options] < data.json > chart.svg

  -i, --input FILE       read JSON from FILE instead of stdin
  -o, --output FILE      write SVG to FILE instead of stdout
  -p, --path PATH        dotted path to an array of samples (repeatable;
                         default: the document root)
  -n, --name NAME        series name for the preceding --path (repeatable)
  -t, --t KEY            timestamp field or index in each sample (default 0)
  -v, --v KEY            value field or index in each sample (default 1)
  -w, --width W          plot width in px (default 640)
  -h, --height H         plot height in px (default 360)
      --pad FRACTION     vertical padding, fraction of value range (default 0.05)
      --window tMin tMax vMin vMax
                         explicit data window instead of auto-fit
      --title TEXT       chart title
      --subtitle TEXT    chart subtitle
      --x-title TEXT     x-axis title
      --y-title TEXT     y-axis title
  -q, --quiet            no report on stderr

Numbers are parsed exactly (no floats). Exit: 0 ok, 1 usage,
2 input/path/number error, 3 timestamps not strictly increasing (or
empty), 4 degenerate window.
"

private def rat (flag s : String) : Except String ℚ :=
  match parseRat s with
  | .ok q => .ok q
  | .error e => .error s!"{flag}: {e}"

def parseArgs : List String → Opts → Except String Opts
  | [], o => .ok o
  | ("-i" :: f :: r), o | ("--input" :: f :: r), o => parseArgs r { o with input := f }
  | ("-o" :: f :: r), o | ("--output" :: f :: r), o => parseArgs r { o with output := f }
  | ("-p" :: p :: r), o | ("--path" :: p :: r), o => parseArgs r { o with paths := o.paths.push p }
  | ("-n" :: n :: r), o | ("--name" :: n :: r), o => parseArgs r { o with names := o.names.push n }
  | ("-t" :: k :: r), o | ("--t" :: k :: r), o => parseArgs r { o with tKey := k }
  | ("-v" :: k :: r), o | ("--v" :: k :: r), o => parseArgs r { o with vKey := k }
  | ("-w" :: s :: r), o | ("--width" :: s :: r), o => do
    let w ← rat "--width" s
    parseArgs r { o with width := w }
  | ("-h" :: s :: r), o | ("--height" :: s :: r), o => do
    let h ← rat "--height" s
    parseArgs r { o with height := h }
  | ("--pad" :: s :: r), o => do
    let p ← rat "--pad" s
    parseArgs r { o with pad := p }
  | ("--window" :: a :: b :: c :: d :: r), o => do
    let a ← rat "--window" a
    let b ← rat "--window" b
    let c ← rat "--window" c
    let d ← rat "--window" d
    parseArgs r { o with window := some (a, b, c, d) }
  | ("--title" :: s :: r), o => parseArgs r { o with title := some s }
  | ("--subtitle" :: s :: r), o => parseArgs r { o with subtitle := some s }
  | ("--x-title" :: s :: r), o => parseArgs r { o with xTitle := some s }
  | ("--y-title" :: s :: r), o => parseArgs r { o with yTitle := some s }
  | ("--x-format" :: f :: r), o =>
    match f with
    | "number" => parseArgs r { o with xFormat := .number }
    | "ms" => parseArgs r { o with xFormat := .epochMs }
    | "s" => parseArgs r { o with xFormat := .epochSeconds }
    | _ => .error s!"--x-format: expected number, ms or s, got {f}"
  | ("--y-decimals" :: n :: r), o =>
    match n.toNat? with
    | some d => parseArgs r { o with yDecimals := some d }
    | none => .error s!"--y-decimals: expected a natural number, got {n}"
  | ("--last-value" :: r), o => parseArgs r { o with lastValue := true }
  | ("-q" :: r), o | ("--quiet" :: r), o => parseArgs r { o with quiet := true }
  | (a :: _), _ => .error s!"unknown or incomplete option: {a}"

/-- Fail with a message on stderr and an exit code. -/
private def die (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln s!"p10t: {msg}"
  pure code

/-- The window: explicit, or fitted to the union of all series with
vertical padding. Rejections name the exact invariant that failed. -/
private def chooseWindow (o : Opts) (all : Array (ℚ × ℚ)) :
    Except (UInt32 × String) Viewport :=
  match o.window with
  | some (a, b, c, d) =>
    match Viewport.tryMk a b c d o.width o.height with
    | some vp => .ok vp
    | none => .error (4, s!"--window rejected: need tMin < tMax ({a} < {b}), " ++
        s!"vMin < vMax ({c} < {d}), width, height > 0")
  | none =>
    match Demos.extent all with
    | none => .error (3, "no data points")
    | some (a, b, c, d) =>
      let padV := o.pad * (d - c)
      match Viewport.tryMk a b (c - padV) (d + padV) o.width o.height with
      | some vp => .ok vp
      | none =>
        if a = b then .error (4, s!"all timestamps equal ({a}); the time window is degenerate")
        else if c = d then .error (4, s!"constant series (value {c}); pass --window to choose a value range")
        else .error (4, "width and height must be positive")

private def q (s : String) : String := Lean.Json.str s |>.compress


def render (args : List String) : IO UInt32 := do
  let o ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"p10t: {e}\n{usage}"; return 1
  let text ← match o.input with
    | some f => IO.FS.readFile f
    | none => do let stdin ← IO.getStdin; stdin.readToEnd
  let doc ← match Lean.Json.parse text with
    | .ok j => pure j
    | .error e => return ← die 2 s!"input is not JSON: {e}"
  let paths := if o.paths.isEmpty then #[""] else o.paths
  let mut series : Array (String × Array (ℚ × ℚ)) := #[]
  for p in paths, i in [0:paths.size] do
    let name := o.names.getD i (if p.isEmpty then "series" else p)
    match extract doc { path := p, t := o.tKey, v := o.vKey } with
    | .ok pts => series := series.push (name, pts)
    | .error e => return ← die 2 s!"{name}: {e}"
  -- data contract, checked by the proven checker
  for (name, pts) in series do
    if pts.isEmpty then return ← die 3 s!"{name}: empty series"
    if !Viewport.strictlyIncreasingFast (pts.map (·.1)).toList then
      let bad := (pts.zip (pts.extract 1 pts.size)).findIdx? fun ((t₁, _), (t₂, _)) => t₂ ≤ t₁
      let at_ := match bad with
        | some i => s!" (sample {i + 1}: {pts[i]!.1} then {pts[i + 1]!.1})"
        | none => ""
      return ← die 3 s!"{name}: timestamps are not strictly increasing{at_}; refusing to draw"
  let vp ← match chooseWindow o (series.flatMap (·.2)) with
    | .ok vp => pure vp
    | .error (code, e) => return ← die code e
  let spec : ChartSpec :=
    { title := o.title, subtitle := o.subtitle, xTitle := o.xTitle, yTitle := o.yTitle,
      xFormat := o.xFormat, yDecimals := o.yDecimals, lastValue := o.lastValue }
  let svg := renderSVG vp series spec
  match o.output with
  | some f => IO.FS.writeFile f svg
  | none => do let out ← IO.getStdout; out.putStr svg
  unless o.quiet do
    let sers := series.map fun (name, pts) =>
      let inW := (Demos.clip vp pts).size
      s!"\{\"name\":{q name},\"points\":{pts.size},\"strictlyIncreasing\":true,\"inWindow\":{inW}}"
    let w := s!"\{\"tMin\":\"{vp.tMin}\",\"tMax\":\"{vp.tMax}\"," ++
      s!"\"vMin\":\"{vp.vMin}\",\"vMax\":\"{vp.vMax}\"," ++
      s!"\"width\":\"{vp.width}\",\"height\":\"{vp.height}\"}"
    IO.eprintln s!"\{\"p10t\":\"render\",\"exact\":true,\"series\":[{",".intercalate sers.toList}],\"window\":{w}}"
  pure 0

end P10t.Cli
