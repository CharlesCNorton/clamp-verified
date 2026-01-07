
type __ = Obj.t

type nat =
| O
| S of nat

type comparison =
| Eq
| Lt
| Gt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val pred : nat -> nat

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

module Nat :
 sig
  val add : nat -> nat -> nat

  val mul : nat -> nat -> nat

  val pow : nat -> nat -> nat
 end

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of int
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : int -> mask

  val sub_mask : int -> int -> mask

  val sub_mask_carry : int -> int -> mask

  val sub : int -> int -> int

  val mul : int -> int -> int

  val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1

  val size_nat : int -> nat

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val ggcdn : nat -> int -> int -> int * (int * int)

  val ggcd : int -> int -> int * (int * int)

  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> nat

  val of_nat : nat -> int

  val of_succ_nat : nat -> int
 end

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val opp : int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val pow_pos : int -> int -> int

  val pow : int -> int -> int

  val compare : int -> int -> comparison

  val sgn : int -> int

  val leb : int -> int -> bool

  val max : int -> int -> int

  val min : int -> int -> int

  val abs : int -> int

  val to_nat : int -> nat

  val of_nat : nat -> int

  val to_pos : int -> int

  val ggcd : int -> int -> int * (int * int)
 end

val z_lt_dec : int -> int -> bool

val z_lt_ge_dec : int -> int -> bool

val z_lt_le_dec : int -> int -> bool

val pow_pos0 : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> 'a1

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

type q = { qnum : int; qden : int }

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qlt_le_dec : q -> q -> bool

val qarchimedean : q -> int

val qpower_positive : q -> int -> q

val qpower : q -> int -> q

val qabs : q -> q

val pos_log2floor_plus1 : int -> int

val qbound_lt_ZExp2 : q -> int

type cReal = { seq : (int -> q); scale : int }

val sig_forall_dec : (nat -> bool) -> nat option

val lowerCutBelow : (q -> bool) -> q

val lowerCutAbove : (q -> bool) -> q

type dReal = (q -> bool)

val dRealQlim_rec : (q -> bool) -> nat -> nat -> q

val dRealAbstr : cReal -> dReal

val dRealQlim : dReal -> nat -> q

val dRealQlimExp2 : dReal -> nat -> q

val cReal_of_DReal_seq : dReal -> int -> q

val cReal_of_DReal_scale : dReal -> int

val dRealRepr : dReal -> cReal

module type RbaseSymbolsSig =
 sig
  type coq_R

  val coq_Rabst : cReal -> coq_R

  val coq_Rrepr : coq_R -> cReal

  val coq_R0 : coq_R

  val coq_R1 : coq_R

  val coq_Rplus : coq_R -> coq_R -> coq_R

  val coq_Rmult : coq_R -> coq_R -> coq_R

  val coq_Ropp : coq_R -> coq_R
 end

module RbaseSymbolsImpl :
 RbaseSymbolsSig

val clamp : int -> int -> int -> int

val clamp_safe : int -> int -> int -> int option

val clamp_R : float -> float -> float -> float

val clamp_list : int list -> int -> int -> int list

val check_bounds : int -> int -> int -> bool

type safe_int =
  int
  (* singleton inductive, whose constructor was mk_safe_int *)

val clamp_verified : int -> int -> int -> safe_int -> safe_int -> safe_int

val clamp_checked : int -> int -> int -> int -> int -> int * bool

val clamp_int63_verified : int -> safe_int -> safe_int -> safe_int

val check_int63_bounds : int -> bool

val clamp_int63_checked : int -> int -> int -> int * bool
