
type comparison =
| Eq
| Lt
| Gt

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Stdlib.Int.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1 **)

  let rec iter f x n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt
 end

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val sub : int -> int -> int **)

  let sub = (-)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val pow_pos : int -> int -> int **)

  let pow_pos z0 =
    Pos.iter (mul z0) 1

  (** val pow : int -> int -> int **)

  let pow x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> pow_pos x p)
      (fun _ -> 0)
      y

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val max : int -> int -> int **)

  let max = Stdlib.max

  (** val min : int -> int -> int **)

  let min = Stdlib.min
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val clamp : int -> int -> int -> int **)

let clamp x lo hi =
  Z.max (Z.min lo hi) (Z.min x (Z.max lo hi))

(** val clamp_safe : int -> int -> int -> int option **)

let clamp_safe x lo hi =
  if Z.leb lo hi then Some (clamp x lo hi) else None

(** val iNT63_MIN : int **)

let iNT63_MIN =
  Z.opp
    (Z.pow ((fun p->2*p) 1) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) 1))))))

(** val iNT63_MAX : int **)

let iNT63_MAX =
  Z.sub
    (Z.pow ((fun p->2*p) 1) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) 1)))))) 1

(** val clamp_list : int list -> int -> int -> int list **)

let clamp_list xs lo hi =
  map (fun x -> clamp x lo hi) xs

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

(** val clamp_checked : int -> int -> int -> int -> int -> int * bool **)

let clamp_checked mIN mAX x lo hi =
  let result = clamp x lo hi in
  (result,
  ((&&) ((&&) (check_bounds mIN mAX lo) (check_bounds mIN mAX hi))
    (check_bounds mIN mAX result)))

(** val clamp_int63_verified : int -> safe_int -> safe_int -> safe_int **)

let clamp_int63_verified x lo hi =
  clamp_verified iNT63_MIN iNT63_MAX x lo hi

(** val check_int63_bounds : int -> bool **)

let check_int63_bounds =
  check_bounds iNT63_MIN iNT63_MAX

(** val clamp_int63_checked : int -> int -> int -> int * bool **)

let clamp_int63_checked x lo hi =
  clamp_checked iNT63_MIN iNT63_MAX x lo hi
