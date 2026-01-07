
type comparison =
| Eq
| Lt
| Gt

module Pos =
 struct
  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt
 end

module Z =
 struct
  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val gtb : int -> int -> bool **)

  let gtb x y =
    match compare x y with
    | Gt -> true
    | _ -> false

  (** val max : int -> int -> int **)

  let max = Stdlib.max

  (** val min : int -> int -> int **)

  let min = Stdlib.min
 end

(** val clamp : int -> int -> int -> int **)

let clamp x lo hi =
  let lo' = Z.min lo hi in
  let hi' = Z.max lo hi in
  if Z.ltb x lo' then lo' else if Z.gtb x hi' then hi' else x

(** val check_bounds : int -> int -> int -> bool **)

let check_bounds mIN mAX z0 =
  (&&) (Z.leb mIN z0) (Z.leb z0 mAX)

type safe_int =
  int
  (* singleton inductive, whose constructor was mk_safe_int *)

(** val clamp_verified :
    int -> int -> int -> safe_int -> safe_int -> safe_int **)

let clamp_verified _ _ =
  clamp
