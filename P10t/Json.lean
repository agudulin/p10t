/-
Exact JSON input. Lean's parser keeps mantissa and decimal exponent, so
`toRat` is lossless (`toRat_exact`). Series selection is plain plumbing.
-/
import Lean.Data.Json
import P10t.Basic

namespace P10t.Json

open Lean

/-- Exact value of a JSON number: `mantissa · 10^(−exponent)`. -/
def toRat (n : JsonNumber) : ℚ :=
  (n.mantissa : ℚ) / (10 : ℚ) ^ n.exponent

/-- Lossless: scaling back by the exponent returns the mantissa. -/
theorem toRat_exact (n : JsonNumber) :
    toRat n * (10 : ℚ) ^ n.exponent = n.mantissa := by
  unfold toRat
  have h : (10 : ℚ) ^ n.exponent ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- Exact rational of a JSON value; numeric strings accepted. -/
def ratOf : Lean.Json → Except String ℚ
  | .num n => .ok (toRat n)
  | .str s =>
    match Lean.Json.parse s with
    | .ok (.num n) => .ok (toRat n)
    | _ => .error s!"not a number: \"{s}\""
  | j => .error s!"expected a number, got {j.compress.take 60}"

/-- Object field or array index. -/
def step (j : Lean.Json) (k : String) : Except String Lean.Json :=
  match j, k.toNat? with
  | .arr a, some i =>
    match a[i]? with
    | some v => .ok v
    | none => .error s!"index {i} out of range (array has {a.size} elements)"
  | .obj _, _ =>
    match j.getObjVal? k with
    | .ok v => .ok v
    | .error _ => .error s!"no field \"{k}\""
  | _, _ => .error s!"cannot index into {j.compress.take 40} with \"{k}\""

/-- Dotted path, e.g. `data.prices`. -/
def getPath (j : Lean.Json) (path : String) : Except String Lean.Json :=
  if path.isEmpty then .ok j else
  (path.splitOn ".").foldlM step j

/-- Where a series lives. -/
structure Selector where
  path : String := ""   -- dotted path; empty = root
  t : String := "0"     -- field or index of the timestamp
  v : String := "1"     -- field or index of the value
  deriving Repr

/-- Samples at `path`: an array of `[t, v]` pairs / objects with fields
`t`, `v`, or an object of two parallel arrays named `t`, `v`. -/
def extract (doc : Lean.Json) (sel : Selector) : Except String (Array (ℚ × ℚ)) := do
  match ← getPath doc sel.path with
  | .arr items =>
    items.mapM fun item => do
      let t ← ratOf (← step item sel.t)
      let v ← ratOf (← step item sel.v)
      pure (t, v)
  | o@(.obj _) =>
    let .arr ts ← step o sel.t | throw s!"field \"{sel.t}\" is not an array"
    let .arr vs ← step o sel.v | throw s!"field \"{sel.v}\" is not an array"
    if ts.size != vs.size then
      throw s!"\"{sel.t}\" has {ts.size} entries but \"{sel.v}\" has {vs.size}"
    (ts.zip vs).mapM fun (tj, vj) => do pure (← ratOf tj, ← ratOf vj)
  | _ => throw s!"path \"{sel.path}\" is neither an array nor an object"

/-- Exact rational from text (`0.05`, `-3`, `1e-7`). -/
def parseRat (s : String) : Except String ℚ :=
  match Lean.Json.parse s with
  | .ok j => ratOf j
  | .error e => .error s!"not a number: \"{s}\" ({e})"

end P10t.Json
