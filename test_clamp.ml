(* Test the extracted clamp function *)

(* Include the extracted code inline for testing *)
type comparison = Eq | Lt | Gt

module Z = struct
  let compare x y = if x = y then Eq else if x < y then Lt else Gt
  let ltb x y = match compare x y with Lt -> true | _ -> false
  let gtb x y = match compare x y with Gt -> true | _ -> false
  let max = Stdlib.max
  let min = Stdlib.min
end

let clamp x lo hi =
  let lo' = Z.min lo hi in
  let hi' = Z.max lo hi in
  if Z.ltb x lo' then lo' else if Z.gtb x hi' then hi' else x

(* Tests *)
let () =
  (* Basic cases *)
  assert (clamp 5 0 10 = 5);
  assert (clamp (-5) 0 10 = 0);
  assert (clamp 15 0 10 = 10);
  
  (* Edge cases *)
  assert (clamp 0 0 10 = 0);
  assert (clamp 10 0 10 = 10);
  
  (* Swapped bounds (lo > hi) *)
  assert (clamp 5 10 0 = 5);
  assert (clamp (-5) 10 0 = 0);
  assert (clamp 15 10 0 = 10);
  
  (* Idempotence *)
  assert (clamp (clamp 5 0 10) 0 10 = clamp 5 0 10);
  assert (clamp (clamp (-5) 0 10) 0 10 = clamp (-5) 0 10);
  assert (clamp (clamp 15 0 10) 0 10 = clamp 15 0 10);
  assert (clamp (clamp 5 10 0) 10 0 = clamp 5 10 0);
  
  (* Equal bounds *)
  assert (clamp 5 5 5 = 5);
  assert (clamp 0 5 5 = 5);
  assert (clamp 10 5 5 = 5);
  
  print_endline "All tests passed!"
