/-
UTC calendar arithmetic for epoch-millisecond axes (display only),
on top of `Std.Time`.
-/
import Std.Time

namespace P10t.Time

open Std.Time

def msPerDay : Int := 86400000

/-- UTC calendar time of an epoch millisecond. -/
def utc (ms : Int) : PlainDateTime :=
  (DateTime.ofTimestampWithZone
    (Timestamp.ofMillisecondsSinceUnixEpoch (Millisecond.Offset.ofInt ms)) TimeZone.UTC)
    |>.toPlainDateTime

/-- Midnight UTC, in ms, of the first day of `d`'s month. -/
def monthStartMs (d : PlainDate) : Int :=
  (d.withDaysClip 1).toEpochDay.val * msPerDay

/-- Tick at `ms` for a visible span of `spanMs`. -/
def formatTick (spanMs ms : Int) : String :=
  let d := utc ms
  if spanMs < 3 * msPerDay then d.format "MMM d HH:mm"
  else if spanMs < 400 * msPerDay then d.format "MMM d"
  else d.format "MMM u"

end P10t.Time
