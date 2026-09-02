/-
# p10t — tick placement (unverified, display only)

Round-number tick values for numeric axes and calendar-aligned tick
values for epoch axes. Tick *values* are exact rationals; only their
screen positions go through the verified `mapX`/`mapY`, so every label
sits exactly at the value it names. The choice of values is a matter
of taste, not correctness, and lives here in the backend.
-/
import P10t.Basic
import P10t.Time

namespace P10t.Ticks

open Std.Time

/-- The 1-2-5 step for `range` aiming at about `target` intervals, with
the number of decimals its labels need. -/
def niceStep (range : ℚ) (target : Nat) : ℚ × Nat :=
  let t : ℚ := max target 1
  let k := Int.log 10 (range / t)
  let base := (10 : ℚ) ^ k
  let best := ([base, 2 * base, 5 * base, 10 * base].argmin fun s => |range / s - t|).getD base
  let decimals := if best.den == 1 then 0 else
    -- `best = m·10^k` with m ∈ {1,2,5,10}; decimals needed = -k (or -k-1 for 10·base)
    (if k < 0 then (-k).toNat else 0)
  (best, decimals)

/-- Multiples of `step` inside `[lo, hi]`, at most `cap` of them. -/
def multiples (lo hi step : ℚ) (cap : Nat := 64) : Array ℚ :=
  if step ≤ 0 then #[] else
  let first : ℚ := ⌈lo / step⌉ * step
  (Array.range cap).map (fun (i : ℕ) => first + i * step) |>.takeWhile (· ≤ hi)

/-- Numeric ticks for `[lo, hi]`: values and labels' decimals. -/
def numeric (lo hi : ℚ) (target : Nat) : Array ℚ × Nat :=
  if hi ≤ lo then (#[], 0) else
  let (step, d) := niceStep (hi - lo) target
  (multiples lo hi step, d)

/-! ## Epoch axes -/

/-- What one step of a date axis is. -/
inductive DateStep where
  | ms (n : Int)        -- fixed length: minutes, hours, days
  | months (n : Nat)
  deriving Repr

def minute : Int := 60000
def hour : Int := 3600000
def day : Int := 86400000

/-- Fixed-length steps from 1 minute to 2 weeks, then months and years. -/
def dateSteps : List DateStep :=
  [1, 2, 5, 10, 15, 30].map (fun n => .ms (n * minute)) ++
  [1, 2, 3, 6, 12].map (fun n => .ms (n * hour)) ++
  [1, 2, 7, 14].map (fun n => .ms (n * day)) ++
  [1, 2, 3, 6].map (fun n => .months n) ++
  [1, 2, 5, 10, 20, 50, 100].map (fun n => .months (12 * n))

/-- Approximate length of a step, for choosing one. -/
def approxMs : DateStep → ℚ
  | .ms n => n
  | .months n => n * (3044 / 100) * day

/-- Pick the step whose count over `spanMs` is closest to `target`. -/
def pickDateStep (spanMs : Int) (target : Nat) : DateStep :=
  let t : ℚ := max target 1
  (dateSteps.argmin fun s => |spanMs / approxMs s - t|).getD (.ms day)

/-- Tick instants (ms) inside `[lo, hi]` for a step, aligned to UTC
boundaries: multiples of the step since the epoch for fixed steps
(so hours and days start on the hour and at midnight), month starts
for month steps. -/
def dateTicks (lo hi : Int) (step : DateStep) (cap : Nat := 64) : Array Int :=
  match step with
  | .ms n =>
    if n ≤ 0 then #[] else
    let first := ⌈(lo : ℚ) / n⌉ * n
    (Array.range cap).map (fun (i : ℕ) => first + i * n) |>.takeWhile (· ≤ hi)
  | .months n =>
    if n = 0 then #[] else
    -- first month start ≥ lo, snapped to a multiple of `n` months from January
    let d := (Time.utc lo).date
    let start := d.subMonthsClip (Month.Offset.ofNat ((d.month.toNat - 1) % n))
    (Array.range (cap + 1)).map (fun (i : ℕ) =>
        Time.monthStartMs (start.addMonthsClip (Month.Offset.ofNat (i * n))))
      |>.takeWhile (· ≤ hi) |>.filter (lo ≤ ·)

/-- Label for a tick at `ms` under a step: clock time for sub-day steps
(with the date at midnight), day for day steps, month for month steps,
year for year steps. -/
def dateLabel (step : DateStep) (ms : Int) : String :=
  let d := Time.utc ms
  let midnight := d.hour.toNat = 0 && d.minute.toNat = 0
  let jan1 := d.month.toNat = 1 && d.day.toNat = 1
  match step with
  | .ms n =>
    if n < day then d.format (if midnight then "MMM d" else "HH:mm")
    else d.format (if jan1 then "u" else "MMM d")
  | .months n => d.format (if n ≥ 12 || d.month.toNat = 1 then "u" else "MMM")

/-- Ticks for an epoch axis `[lo, hi]` in `unit` ms per data unit
(`1` for milliseconds, `1000` for seconds): exact data values with labels. -/
def epoch (lo hi : ℚ) (unit : Int) (target : Nat) : Array (ℚ × String) :=
  let loMs := ⌊lo * unit⌋
  let hiMs := ⌈hi * unit⌉
  if hiMs ≤ loMs then #[] else
  let step := pickDateStep (hiMs - loMs) target
  (dateTicks loMs hiMs step).map fun (ms : Int) => ((ms : ℚ) / (unit : ℚ), dateLabel step ms)

end P10t.Ticks
