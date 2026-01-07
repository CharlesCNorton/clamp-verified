
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

  val ltb : int -> int -> bool

  val gtb : int -> int -> bool

  val max : int -> int -> int

  val min : int -> int -> int
 end

val clamp : int -> int -> int -> int
