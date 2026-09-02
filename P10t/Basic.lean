/-
Verified layout core: maps `[tMin, tMax] × [vMin, vMax]` onto
`[0, width] × [0, height]` over ℚ; every layout property is a theorem.
"Correct" / "complete" follow Melquiond, *Plotting in a Formally
Verified Way* (2021); see README.
-/
import Mathlib

set_option autoImplicit false

namespace P10t

/-! ## Viewport -/

/-- Data window → screen rectangle. The invariants are proof fields, so
no degenerate viewport can be constructed. -/
structure Viewport where
  tMin : ℚ
  tMax : ℚ
  vMin : ℚ
  vMax : ℚ
  width : ℚ
  height : ℚ
  ht : tMin < tMax
  hv : vMin < vMax
  hw : 0 < width
  hh : 0 < height

namespace Viewport

/-- `some` iff the invariants hold. -/
def tryMk (tMin tMax vMin vMax width height : ℚ) : Option Viewport :=
  if h : tMin < tMax ∧ vMin < vMax ∧ 0 < width ∧ 0 < height then
    some { tMin, tMax, vMin, vMax, width, height,
           ht := h.1, hv := h.2.1, hw := h.2.2.1, hh := h.2.2.2 }
  else none

theorem tryMk_isSome (tMin tMax vMin vMax width height : ℚ) :
    (tryMk tMin tMax vMin vMax width height).isSome ↔
      tMin < tMax ∧ vMin < vMax ∧ 0 < width ∧ 0 < height := by
  simp [tryMk]

/-! ## The scaling function, proven once -/

/-- Affine map `⟦lo, hi⟧ → ⟦0, out⟧`; both axes instantiate it. -/
def scaleInto (lo hi out : ℚ) (x : ℚ) : ℚ :=
  (x - lo) / (hi - lo) * out

variable {lo hi out : ℚ}

/-! ### Correctness (I): order -/

/-- Strictly monotone: the chart never draws backwards. -/
theorem scaleInto_strictMono (hlo : lo < hi) (hout : 0 < out) {x y : ℚ}
    (h : x < y) : scaleInto lo hi out x < scaleInto lo hi out y := by
  have hd : (0 : ℚ) < hi - lo := sub_pos.mpr hlo
  have hsub : x - lo < y - lo := sub_lt_sub_right h lo
  unfold scaleInto
  gcongr

theorem scaleInto_mono (hlo : lo < hi) (hout : 0 < out) {x y : ℚ}
    (h : x ≤ y) : scaleInto lo hi out x ≤ scaleInto lo hi out y := by
  rcases lt_or_eq_of_le h with h' | rfl
  · exact (scaleInto_strictMono hlo hout h').le
  · rfl

/-! ### Correctness (II): an honest affine image -/

/-- Screen gap = data gap × exact scale. -/
theorem scaleInto_sub (x y : ℚ) :
    scaleInto lo hi out y - scaleInto lo hi out x
      = (y - x) * (out / (hi - lo)) := by
  unfold scaleInto
  ring

theorem scaleInto_sub_pos (hlo : lo < hi) (hout : 0 < out) {x y : ℚ}
    (h : x < y) : 0 < scaleInto lo hi out y - scaleInto lo hi out x := by
  rw [scaleInto_sub]
  exact mul_pos (sub_pos.mpr h) (div_pos hout (sub_pos.mpr hlo))

/-! ### Completeness: exact endpoints, nothing off canvas -/

theorem scaleInto_lo : scaleInto lo hi out lo = 0 := by
  simp [scaleInto]

theorem scaleInto_hi (hlo : lo < hi) :
    scaleInto lo hi out hi = out := by
  have hd : (0 : ℚ) < hi - lo := sub_pos.mpr hlo
  simp [scaleInto, div_self hd.ne']

/-- In-window data stays inside the screen rectangle. -/
theorem scaleInto_mem (hlo : lo < hi) (hout : 0 < out) {x : ℚ}
    (h : x ∈ Set.Icc lo hi) : scaleInto lo hi out x ∈ Set.Icc 0 out :=
  Set.mem_Icc.mpr
    ⟨calc (0 : ℚ) = scaleInto lo hi out lo := scaleInto_lo.symm
        _ ≤ scaleInto lo hi out x := scaleInto_mono hlo hout h.1,
      calc scaleInto lo hi out x ≤ scaleInto lo hi out hi :=
          scaleInto_mono hlo hout h.2
        _ = out := scaleInto_hi hlo⟩

/-! ## Axis maps -/

def mapX (vp : Viewport) (t : ℚ) : ℚ :=
  scaleInto vp.tMin vp.tMax vp.width t

/-- Grows upward; the backend flips it for SVG. -/
def mapY (vp : Viewport) (v : ℚ) : ℚ :=
  scaleInto vp.vMin vp.vMax vp.height v

theorem mapX_strictMono (vp : Viewport) {t₁ t₂ : ℚ} (h : t₁ < t₂) :
    vp.mapX t₁ < vp.mapX t₂ :=
  scaleInto_strictMono vp.ht vp.hw h

theorem mapY_strictMono (vp : Viewport) {v₁ v₂ : ℚ} (h : v₁ < v₂) :
    vp.mapY v₁ < vp.mapY v₂ :=
  scaleInto_strictMono vp.hv vp.hh h

theorem mapX_mono (vp : Viewport) {t₁ t₂ : ℚ} (h : t₁ ≤ t₂) :
    vp.mapX t₁ ≤ vp.mapX t₂ :=
  scaleInto_mono vp.ht vp.hw h

theorem mapY_mono (vp : Viewport) {v₁ v₂ : ℚ} (h : v₁ ≤ v₂) :
    vp.mapY v₁ ≤ vp.mapY v₂ :=
  scaleInto_mono vp.hv vp.hh h

theorem mapX_sub (vp : Viewport) (t₁ t₂ : ℚ) :
    vp.mapX t₂ - vp.mapX t₁
      = (t₂ - t₁) * (vp.width / (vp.tMax - vp.tMin)) :=
  scaleInto_sub t₁ t₂

theorem mapY_sub (vp : Viewport) (v₁ v₂ : ℚ) :
    vp.mapY v₂ - vp.mapY v₁
      = (v₂ - v₁) * (vp.height / (vp.vMax - vp.vMin)) :=
  scaleInto_sub v₁ v₂

theorem mapX_tMin (vp : Viewport) : vp.mapX vp.tMin = 0 :=
  scaleInto_lo

theorem mapX_tMax (vp : Viewport) : vp.mapX vp.tMax = vp.width :=
  scaleInto_hi vp.ht

theorem mapY_vMin (vp : Viewport) : vp.mapY vp.vMin = 0 :=
  scaleInto_lo

theorem mapY_vMax (vp : Viewport) : vp.mapY vp.vMax = vp.height :=
  scaleInto_hi vp.hv

theorem mapX_mem (vp : Viewport) {t : ℚ} (h : t ∈ Set.Icc vp.tMin vp.tMax) :
    vp.mapX t ∈ Set.Icc 0 vp.width :=
  scaleInto_mem vp.ht vp.hw h

theorem mapY_mem (vp : Viewport) {v : ℚ} (h : v ∈ Set.Icc vp.vMin vp.vMax) :
    vp.mapY v ∈ Set.Icc 0 vp.height :=
  scaleInto_mem vp.hv vp.hh h

/-! ## Window membership -/

/-- Runtime window test; `inWindow_iff` ties it to `Set.Icc`. -/
def inWindow (vp : Viewport) (t v : ℚ) : Bool :=
  decide (vp.tMin ≤ t ∧ t ≤ vp.tMax ∧ vp.vMin ≤ v ∧ v ≤ vp.vMax)

theorem inWindow_iff (vp : Viewport) (t v : ℚ) :
    vp.inWindow t v = true ↔
      t ∈ Set.Icc vp.tMin vp.tMax ∧ v ∈ Set.Icc vp.vMin vp.vMax := by
  simp [inWindow, Set.mem_Icc, and_assoc]

/-- Whatever passes the runtime check lands on the canvas. -/
theorem inWindow_on_canvas (vp : Viewport) {t v : ℚ}
    (h : vp.inWindow t v = true) :
    vp.mapX t ∈ Set.Icc 0 vp.width ∧ vp.mapY v ∈ Set.Icc 0 vp.height := by
  rw [inWindow_iff] at h
  exact ⟨vp.mapX_mem h.1, vp.mapY_mem h.2⟩

/-! ## The data contract: strictly increasing timestamps -/

def strictlyIncreasing (ts : List ℚ) : Bool :=
  decide (ts.Pairwise (· < ·))

theorem strictlyIncreasing_iff (ts : List ℚ) :
    strictlyIncreasing ts = true ↔ ts.Pairwise (· < ·) :=
  decide_eq_true_iff

/-- Linear-time variant (`Pairwise` is quadratic). -/
def strictlyIncreasingFast (ts : List ℚ) : Bool :=
  decide (ts.IsChain (· < ·))

theorem strictlyIncreasingFast_eq (ts : List ℚ) :
    strictlyIncreasingFast ts = strictlyIncreasing ts := by
  simp [strictlyIncreasingFast, strictlyIncreasing, List.isChain_iff_pairwise]

/-- A checked series has strictly increasing screen X. -/
theorem checked_never_draws_backwards (vp : Viewport) {ts : List ℚ}
    (h : strictlyIncreasing ts = true) :
    (ts.map vp.mapX).Pairwise (· < ·) := by
  rw [strictlyIncreasing_iff] at h
  exact h.map _ fun _ _ hlt => mapX_strictMono vp hlt

/-! ## Function plotting -/

/-- A monotone `f` renders order-faithfully. (Full Melquiond correctness
would need interval enclosures per pixel.) -/
theorem sampled_mapY_mono (vp : Viewport) {f : ℚ → ℚ}
    (hf : Monotone f) {ts : List ℚ} (hts : ts.Pairwise (· < ·)) :
    (ts.map fun t => vp.mapY (f t)).Pairwise (· ≤ ·) :=
  hts.map _ fun _ _ hab => mapY_mono vp (hf hab.le)

/-! ## Zoom and pan: total, so the invariants carry through -/

/-- Zoom about `c` by `f` (`f > 1` zooms in). -/
def zoom (vp : Viewport) (c : ℚ) (f : ℚ) (hf : 0 < f) : Viewport where
  tMin := c + (vp.tMin - c) / f
  tMax := c + (vp.tMax - c) / f
  vMin := vp.vMin
  vMax := vp.vMax
  width := vp.width
  height := vp.height
  ht := by
    have h1 : vp.tMin - c < vp.tMax - c := sub_lt_sub_right vp.ht c
    gcongr
  hv := vp.hv
  hw := vp.hw
  hh := vp.hh

/-- Pan the time window by `δ`. -/
def pan (vp : Viewport) (δ : ℚ) : Viewport where
  tMin := vp.tMin + δ
  tMax := vp.tMax + δ
  vMin := vp.vMin
  vMax := vp.vMax
  width := vp.width
  height := vp.height
  ht := by
    have h : vp.tMin < vp.tMax := vp.ht
    gcongr
  hv := vp.hv
  hw := vp.hw
  hh := vp.hh

end Viewport

/-! ## Melquiond's `plot2` for monotone functions

A plot is a list of pixel-row bands `(y₁, y₂)`, one per column; it is
correct when `f x ∈ [oy + dy·y₁, oy + dy·y₂]` throughout each column.
For monotone `f` that reduces to two exact evaluations per column. -/

namespace Melquiond

/-- Band `r` encloses `f` on the column `[a, a + dx]`. -/
def ColumnEncloses (f : ℚ → ℚ) (a dx oy dy : ℚ) (r : ℤ × ℤ) : Prop :=
  ∀ x, a ≤ x → x ≤ a + dx → oy + dy * r.1 ≤ f x ∧ f x ≤ oy + dy * r.2

/-- Exact check at the column edges. -/
def columnCheck (f : ℚ → ℚ) (a dx oy dy : ℚ) (r : ℤ × ℤ) : Bool :=
  decide (oy + dy * r.1 ≤ f a ∧ f (a + dx) ≤ oy + dy * r.2)

/-- For monotone `f` the edge check proves the column. -/
theorem columnEncloses_of_monotoneOn {f : ℚ → ℚ} {a dx oy dy : ℚ}
    {r : ℤ × ℤ} (hdx : 0 ≤ dx) (hf : MonotoneOn f (Set.Icc a (a + dx)))
    (h : columnCheck f a dx oy dy r = true) :
    ColumnEncloses f a dx oy dy r := by
  simp only [columnCheck, decide_eq_true_eq] at h
  intro x h1 h2
  have hx : x ∈ Set.Icc a (a + dx) := ⟨h1, h2⟩
  have hl : a ∈ Set.Icc a (a + dx) := ⟨le_rfl, by linarith⟩
  have hr : a + dx ∈ Set.Icc a (a + dx) := ⟨by linarith, le_rfl⟩
  exact ⟨h.1.trans (hf hl hx h1), (hf hx hr h2).trans h.2⟩

/-- Every column, first one starting at `a`. -/
def plotCheck (f : ℚ → ℚ) (dx oy dy : ℚ) : ℚ → List (ℤ × ℤ) → Bool
  | _, [] => true
  | a, r :: rs => columnCheck f a dx oy dy r && plotCheck f dx oy dy (a + dx) rs

/-- Passing `plotCheck` with `f` monotone on a set covering every column
proves every column. -/
theorem plotCheck_encloses {f : ℚ → ℚ} {dx oy dy : ℚ} (hdx : 0 ≤ dx)
    {S : Set ℚ} (hf : MonotoneOn f S) :
    ∀ (a : ℚ) (bands : List (ℤ × ℤ)),
      (∀ j : ℕ, j < bands.length →
        Set.Icc (a + dx * j) (a + dx * j + dx) ⊆ S) →
      plotCheck f dx oy dy a bands = true →
      ∀ (j : ℕ) (hj : j < bands.length),
        ColumnEncloses f (a + dx * j) dx oy dy bands[j]
  | _, [], _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | a, r :: rs, hS, h, 0, _ => by
    have h0 : columnCheck f a dx oy dy r = true := by
      simp [plotCheck] at h; exact h.1
    have hsub : Set.Icc a (a + dx) ⊆ S := by
      simpa using hS 0 (by simp)
    simpa using columnEncloses_of_monotoneOn hdx (hf.mono hsub) h0
  | a, r :: rs, hS, h, j + 1, hj => by
    have hrest : plotCheck f dx oy dy (a + dx) rs = true := by
      simp [plotCheck] at h; exact h.2
    have hS' : ∀ j : ℕ, j < rs.length →
        Set.Icc (a + dx + dx * j) (a + dx + dx * j + dx) ⊆ S := by
      intro j hj
      have := hS (j + 1) (by simpa using Nat.succ_lt_succ hj)
      convert this using 2 <;> push_cast <;> ring
    have ih := plotCheck_encloses hdx hf (a + dx) rs hS' hrest j
      (by simpa using hj)
    have e : a + dx + dx * j = a + dx * ((j : ℚ) + 1) := by ring
    simpa [e] using ih

end Melquiond

end P10t
