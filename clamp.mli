
type comparison =
| Eq
| Lt
| Gt

module Pos :
 sig
  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison
 end

module Z :
 sig
  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val gtb : int -> int -> bool

  val max : int -> int -> int

  val min : int -> int -> int
 end

val clamp : int -> int -> int -> int

val check_bounds : int -> int -> int -> bool

type safe_int =
  int
  (* singleton inductive, whose constructor was mk_safe_int *)

val clamp_verified : int -> int -> int -> safe_int -> safe_int -> safe_int
