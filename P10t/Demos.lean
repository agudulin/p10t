/-
Demos: each shows what the verified core does about one real chart
bug. They only use the library.
-/
import P10t.Render

namespace P10t.Demos

/-! ## Gallery -/

structure Panel where
  svg : String
  w : Float
  h : Float

/-- One chart; title and caption go through `ChartSpec`. -/
def panel (title caption : String) (vp : Viewport)
    (series : Array (String × Array (ℚ × ℚ))) : Panel :=
  let (svg, w, h) := renderSized vp series { title, subtitle := caption }
  { svg, w, h }

/-- Panels left to right. -/
def gallery (panels : Array Panel) (theme : Theme := {}) : String :=
  let gap : Float := 28
  let (body, x, maxH) := panels.foldl (fun (acc, x, mh) p =>
    let g := s!"<g transform=\"translate({fmt x},0)\">{p.svg}</g>"
    (acc ++ g, x + p.w + gap, max mh p.h))
    ("", (0 : Float), (0 : Float))
  let w := fmt (x - gap)
  let h := fmt maxH
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{w}\" height=\"{h}\" " ++
  s!"viewBox=\"0 0 {w} {h}\">" ++
  (if theme.pagePlane == "none" then "" else
    s!"<rect width=\"{w}\" height=\"{h}\" fill=\"{theme.pagePlane}\"/>") ++
  s!"{body}</svg>"

/-! ## Helpers -/

/-- `n + 1` exact samples of `fn` on `⟦tMin, tMax⟧`. -/
def samples (fn : ℚ → ℚ) (n : ℕ) (tMin tMax : ℚ) : Array (ℚ × ℚ) :=
  let steps := max n 1
  Array.range (n + 1) |>.map fun (i : ℕ) =>
    let t := tMin + (tMax - tMin) * i / steps
    (t, fn t)

/-- Bounding box of a series, `none` when empty. -/
def extent (pts : Array (ℚ × ℚ)) : Option (ℚ × ℚ × ℚ × ℚ) :=
  if h : 0 < pts.size then
    let (t, v) := pts[0]
    some <| pts.foldl (fun (a, b, c, d) (t, v) =>
      (min a t, max b t, min c v, max d v)) (t, t, v, v)
  else none

/-- Fit a window to the data; `none` when the data cannot define one. -/
def autoFit (pts : Array (ℚ × ℚ)) (w h : ℚ) (pad : ℚ := 0) :
    Option Viewport := do
  let (a, b, c, d) ← extent pts
  Viewport.tryMk a b (c - pad) (d + pad) w h

/-- Points inside the window. -/
def clip (vp : Viewport) (pts : Array (ℚ × ℚ)) : Array (ℚ × ℚ) :=
  pts.filter fun (t, v) => vp.inWindow t v

def cubic (t : ℚ) : ℚ := t ^ 3 - 6 * t ^ 2 + 9 * t

def parabola (t : ℚ) : ℚ := t ^ 2 - 4 * t + 3

/-! ## Demo 1: two series -/

def demoBasic : String :=
  match Viewport.tryMk 0 4 (-3 / 2) (9 / 2) 586 326 with
  | some vp =>
    renderSVG vp
      #[("f(t) = t³ − 6t² + 9t", samples cubic 200 0 4),
        ("g(t) = t² − 4t + 3", samples parabola 200 0 4)]
      { title := "Two exact-rational curves",
        subtitle := "Sampled at 201 points on [0, 4] · verified layout, delegated rasterization",
        xTitle := "t (time)", yTitle := "value", watermark := "P10T" }
  | none => ""

/-! ## Demo 2: Melquiond §2 — his band list for `x²`, checked by
`plotCheck` and drawn inside his §4 envelope -/

namespace Paper

def ox : ℚ := 0
def dx : ℚ := 820 / 8192
def oy : ℚ := -5 / 16384
def dy : ℚ := 665 / 65536
def hPx : ℕ := 100

def bands : List (ℤ × ℤ) :=
  [(0, 2), (0, 5), (3, 9), (8, 16), (15, 25),
   (24, 36), (35, 49), (48, 64), (62, 81), (79, 100)]

def f (x : ℚ) : ℚ := x ^ 2

theorem f_monotoneOn : MonotoneOn f (Set.Icc ox (ox + dx * bands.length)) :=
  fun _ ha _ _ hab => pow_le_pow_left₀ ha.1 hab 2

/-- His band list is a correct plot of `x²`: exact computation plus monotonicity. -/
theorem bands_correct :
    ∀ (j : ℕ) (hj : j < bands.length),
      Melquiond.ColumnEncloses f (ox + dx * j) dx oy dy bands[j] :=
  Melquiond.plotCheck_encloses (by norm_num [dx]) f_monotoneOn ox bands
    (fun j hj => by
      have hj' : (j : ℚ) + 1 ≤ bands.length := by exact_mod_cast hj
      apply Set.Icc_subset_Icc
      · norm_num [dx]
      · norm_num [dx] at hj' ⊢; linarith)
    (by decide +kernel)

/-- His §4 lower/upper piecewise-affine enclosures. -/
def envelope : Array (ℚ × ℚ) × Array (ℚ × ℚ) :=
  let arr := bands.toArray
  let n := arr.size
  let at_ (i : ℕ) : ℤ × ℤ := arr.getD (min i (n - 1)) (0, 0)
  let pts (pick : ℤ × ℤ → ℤ × ℤ → ℤ) : Array (ℚ × ℚ) :=
    Array.range (n + 1) |>.map fun i =>
      let l := at_ (i - 1)
      let r := at_ i
      let l := if i = 0 then r else l
      let r := if i = n then l else r
      (ox + dx * i, oy + dy * pick l r)
  (pts fun l r => min l.1 r.1, pts fun l r => max l.2 r.2)

def svg : String :=
  match Viewport.tryMk ox (ox + dx * bands.length) oy (oy + dy * hPx) 500 400 with
  | some vp =>
    let (lo, hi) := envelope
    renderSVG vp
      #[("f(x) = x², exact samples", samples f 100 ox (ox + dx * bands.length)),
        ("Melquiond upper enclosure", hi),
        ("Melquiond lower enclosure", lo)]
      { title := "Melquiond §2: f(x) = x², 10 columns × 100 rows",
        subtitle := "His enclosing envelope (arXiv:2108.03974 §4) with our exact curve inside",
        xTitle := "x", yTitle := "f(x)", watermark := "P10T" }
  | none => ""

def report : String :=
  let ok := Melquiond.plotCheck f dx oy dy ox bands
  s!"paper-x2: {bands.length} columns of Melquiond's band list checked exactly over ℚ: {ok}"

end Paper

/-! ## Demo 3: timestamps through float32

At ~1.7·10¹² ms a binary32 ulp is 2¹⁷ ms, so a 1-minute series collapses
onto ~2-minute steps. The contract checker rejects it. -/

namespace Float32

def t0 : ℚ := 1700000000000
def minuteMs : ℚ := 60000
def nPts : ℕ := 40
def ulp : ℚ := 2 ^ 17

/-- Synthetic walk. -/
def price (i : ℕ) : ℚ := 62300 + ((i * i * 7) % 53 : ℕ) + (i : ℚ) / 2

def exact : Array (ℚ × ℚ) :=
  Array.range nPts |>.map fun (i : ℕ) => (t0 + minuteMs * (i : ℚ), price i)

/-- Round to the nearest multiple of `u`. -/
def roundToUlp (u t : ℚ) : ℚ := (round (t / u) : ℚ) * u

def corrupted : Array (ℚ × ℚ) := exact.map fun (t, v) => (roundToUlp ulp t, v)

def timesOk (pts : Array (ℚ × ℚ)) : Bool :=
  Viewport.strictlyIncreasing (pts.map (·.1)).toList

def svg : String :=
  match Viewport.tryMk t0 (t0 + minuteMs * (nPts + 1)) 62290 62370 520 300 with
  | some vp =>
    gallery #[
      panel "Exact ℚ timestamps" "strictlyIncreasing = true → drawn"
        vp #[("1-minute series", exact)],
      panel "Same series, timestamps stored as float32"
        "strictlyIncreasing = false → p10t refuses; this is what a naive plotter draws"
        vp #[("collapsed to 131072 ms steps", corrupted)]]
  | none => ""

def report : String :=
  let distinct := (corrupted.map (·.1)).toList.eraseDups.length
  s!"float32-timestamps: exact series passes strictlyIncreasing: {timesOk exact}; " ++
  s!"float32-rounded series passes: {timesOk corrupted} " ++
  s!"({nPts} points collapsed onto {distinct} distinct timestamps)"

end Float32

/-! ## Demo 4: degenerate windows — `tryMk` returns `none` where a float
pipeline would produce NaN -/

namespace Degenerate

def flat : Array (ℚ × ℚ) := Array.range 20 |>.map fun (i : ℕ) => ((i : ℚ), 42)
def single : Array (ℚ × ℚ) := #[(7, 3)]
def empty : Array (ℚ × ℚ) := #[]

private def show_ (name : String) (r : Option Viewport) : String :=
  s!"  {name}: " ++ (if r.isSome then "viewport ok" else "rejected (tryMk = none)")

def report : String :=
  "degenerate windows (plot 400×200):\n" ++
  show_ "constant series, no padding " (autoFit flat 400 200) ++ "\n" ++
  show_ "constant series, padding 1  " (autoFit flat 400 200 1) ++ "\n" ++
  show_ "single sample               " (autoFit single 400 200 1) ++ "\n" ++
  show_ "empty series                " (autoFit empty 400 200 1) ++ "\n" ++
  show_ "zero-width canvas           " (autoFit flat 0 200 1)

example : Viewport.tryMk 0 19 42 42 400 200 = none := by
  simp [Viewport.tryMk]

example : Viewport.tryMk 7 7 2 4 400 200 = none := by
  simp [Viewport.tryMk]

end Degenerate

/-! ## Demo 5: zoom and pan — each frame is `zoom`/`pan` of the previous
one, so the invariants hold by construction -/

namespace ZoomPan

def data : Array (String × Array (ℚ × ℚ)) :=
  #[("f(t) = t³ − 6t² + 9t", samples cubic 400 0 4),
    ("g(t) = t² − 4t + 3", samples parabola 400 0 4)]

def frame (title caption : String) (vp : Viewport) : Panel :=
  panel title caption vp (data.map fun (n, pts) => (n, clip vp pts))

def svg : String :=
  match Viewport.tryMk 0 4 (-3 / 2) (9 / 2) 360 240 with
  | some vp0 =>
    let vp1 := vp0.zoom 2 2 (by norm_num)
    let vp2 := vp1.zoom (5 / 2) 2 (by norm_num)
    let vp3 := vp2.pan (-3 / 2)
    gallery #[
      frame "Full window" "t ∈ [0, 4]" vp0,
      frame "zoom ×2 about t = 2" "t ∈ [1, 3]" vp1,
      frame "then zoom ×2 about t = 2.5" "t ∈ [1.75, 2.75]" vp2,
      frame "then pan by −1.5" "t ∈ [0.25, 1.25], window still valid" vp3]
  | none => ""

end ZoomPan

end P10t.Demos
