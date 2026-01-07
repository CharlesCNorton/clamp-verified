
type comparison =
| Eq
| Lt
| Gt

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val mul : int -> int -> int

  val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison
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

  val leb : int -> int -> bool

  val max : int -> int -> int

  val min : int -> int -> int
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val clamp : int -> int -> int -> int

val clamp_safe : int -> int -> int -> int option

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
