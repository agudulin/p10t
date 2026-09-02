```
-- What

Plotting code fails quietly on edge cases: a flat series divides by
zero, floats put a point a pixel off, an axis gets flipped.

p10t renders time series to SVG. The number-to-pixel step is proven in
Lean 4; the kernel checks it on every build. If the proof obligations
can't be met for your input, it exits nonzero and says why.
```

```
-- The contract

Exit code 0 means:

  - left is earlier, up is bigger.
  - twice the gap in data is twice the gap on screen. exact rationals.
  - first/last t sit on the left/right edge. min/max v on bottom/top.
  - every point inside the window is on the canvas.
  - zoom/pan can't produce a window that breaks the above.
  - JSON 101.25 is read as 405/4, not the nearest float.
```

```
-- Use

  lake build
  lake exe p10t render --path prices < data.json > chart.svg
  lake exe p10t render --path hourly --t time --v temperature_2m --x-format s \
      < open-meteo.json > temp.svg

Input is {"prices": [[t, v], ...]}, objects (--t/--v), or parallel
arrays as Open-Meteo returns them. --x-format ms|s for epoch time.
--help for the rest.

  0  chart written
  1  bad flags
  2  not json / path missing / not a number
  3  timestamps not strictly increasing, or empty
  4  no valid window: constant series or degenerate --window

One JSON line goes to stderr per run: points parsed, checks passed,
window chosen. Keep it with the SVG.
```

```
-- From Lean

  open P10t
  let some vp := Viewport.tryMk 0 4 (-3/2) (9/2) 640 360 | ...  -- none = degenerate
  let svg := renderSVG vp #[("series", pts)] { title := "x" }

tryMk returns none for a degenerate viewport. zoom and pan are total
and return a Viewport, so its proof fields hold. Styling is one record
in P10t/Theme.lean.
```

```
-- How

  json --parse--> exact Q --verified layout--> exact Q coords --Q->Float--> svg
                                                               (display only)

P10t/Basic.lean holds the theorems. Json.lean parses exactly,
Render.lean prints coordinates that are already proven.

  never backwards        mapX_strictMono  mapY_strictMono
  distances exact        mapX_sub  mapY_sub
  edges are the data     mapX_tMin  mapX_tMax  mapY_vMin  mapY_vMax
  nothing lost           mapX_mem  mapY_mem  inWindow_on_canvas
  no div by zero         proof fields on Viewport
  zoom/pan sane          zoom, pan : ... -> Viewport
  contract check right   strictlyIncreasing_iff  checked_never_draws_backwards
  numbers read exactly   toRat_exact

Correctness follows Melquiond, "Plotting in a Formally Verified Way"
(2021): draw nothing not in the data, miss nothing that is. His §2
example is in P10t/Demos.lean, proven by decide +kernel
(Paper.bands_correct).

Read more in the original paper: https://arxiv.org/pdf/2108.03974v1
```
