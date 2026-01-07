(* IEEE 754 Float Clamp - Verified Implementation

   This implementation corresponds to the Coq specification in Clamp.v.
   The theorems clamp_ieee_* prove correctness of this implementation.

   IEEE 754 semantics:
   - NaN in any operand propagates to result (quiet NaN)
   - +∞ clamps to upper bound, -∞ clamps to lower bound
   - Swapped bounds (lo > hi) are normalized via min/max
   - Negative zero equals positive zero for comparison purposes
*)

(** [clamp_float x lo hi] bounds [x] to the interval [min(lo,hi), max(lo,hi)].

    NaN handling: If any input is NaN, returns NaN.
    Infinity handling: +∞ clamps to max(lo,hi), -∞ clamps to min(lo,hi).

    Verified properties (from Clamp.v):
    - clamp_ieee_nan_propagates: NaN input → NaN output
    - clamp_ieee_finite_in_bounds: finite inputs → result in [lo', hi']
    - clamp_ieee_symmetric: clamp x lo hi = clamp x hi lo
    - clamp_ieee_preserves_finite: non-NaN inputs → non-NaN output
    - clamp_float_ieee_equiv: matches algebraic specification
*)
let clamp_float (x : float) (lo : float) (hi : float) : float =
  if Float.is_nan x || Float.is_nan lo || Float.is_nan hi then
    Float.nan
  else
    let lo' = Float.min lo hi in
    let hi' = Float.max lo hi in
    Float.max lo' (Float.min x hi')

(** [clamp_float_safe x lo hi] returns [Some v] if lo <= hi, [None] otherwise.

    Use this variant when swapped bounds indicate a caller bug rather than
    a valid alternative representation.
*)
let clamp_float_safe (x : float) (lo : float) (hi : float) : float option =
  if Float.is_nan x || Float.is_nan lo || Float.is_nan hi then
    Some Float.nan
  else if lo <= hi then
    Some (clamp_float x lo hi)
  else
    None

(** [is_clamped x lo hi] returns true if x is within [lo, hi]. *)
let is_clamped (x : float) (lo : float) (hi : float) : bool =
  if Float.is_nan x || Float.is_nan lo || Float.is_nan hi then
    false
  else
    let lo' = Float.min lo hi in
    let hi' = Float.max lo hi in
    lo' <= x && x <= hi'

(** [clamp_float_list xs lo hi] clamps each element of [xs]. *)
let clamp_float_list (xs : float list) (lo : float) (hi : float) : float list =
  List.map (fun x -> clamp_float x lo hi) xs
