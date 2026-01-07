
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val eqb : Float64.t -> Float64.t -> bool **)

let eqb = Float64.eq

(** val leb : Float64.t -> Float64.t -> bool **)

let leb = Float64.le

(** val is_nan : Float64.t -> bool **)

let is_nan f =
  negb (eqb f f)

(** val prim_min : Float64.t -> Float64.t -> Float64.t **)

let prim_min x y =
  if is_nan x then x else if is_nan y then y else if leb x y then x else y

(** val prim_max : Float64.t -> Float64.t -> Float64.t **)

let prim_max x y =
  if is_nan x then x else if is_nan y then y else if leb x y then y else x

(** val clamp_prim : Float64.t -> Float64.t -> Float64.t -> Float64.t **)

let clamp_prim x lo hi =
  if is_nan x
  then x
  else if is_nan lo
       then lo
       else if is_nan hi
            then hi
            else let lo' = prim_min lo hi in
                 let hi' = prim_max lo hi in prim_max lo' (prim_min x hi')
