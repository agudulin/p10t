/-
    p10t                 write the demo charts into `out/`
    p10t demos           same
    p10t render ...      JSON on stdin → SVG on stdout (see `P10t/Cli.lean`)
-/
import P10t.Demos
import P10t.Cli

open P10t.Demos

def demos : IO Unit := do
  IO.FS.createDirAll "out"
  IO.FS.writeFile "out/demo.svg" demoBasic
  IO.FS.writeFile "out/paper-x2.svg" Paper.svg
  IO.FS.writeFile "out/float32-timestamps.svg" Float32.svg
  IO.FS.writeFile "out/zoom-pan.svg" ZoomPan.svg
  IO.println Paper.report
  IO.println Float32.report
  IO.println Degenerate.report
  IO.println "wrote out/demo.svg out/paper-x2.svg out/float32-timestamps.svg out/zoom-pan.svg"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["demos"] => demos; pure 0
  | "render" :: rest => P10t.Cli.render rest
  | ["--help"] | ["-h"] | ["help"] =>
    IO.println "usage: p10t [demos]\n       p10t render [options] < data.json > chart.svg\n       p10t render --help"
    pure 0
  | a :: _ => IO.eprintln s!"p10t: unknown command {a}"; pure 1
