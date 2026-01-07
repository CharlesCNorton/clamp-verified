(* Test the extracted clamp function *)

(* Include the extracted code inline for testing *)
type comparison = Eq | Lt | Gt

module Z = struct
  let compare x y = if x = y then Eq else if x < y then Lt else Gt
  let ltb x y = match compare x y with Lt -> true | _ -> false
  let gtb x y = match compare x y with Gt -> true | _ -> false
  let leb x y = match compare x y with Gt -> false | _ -> true
  let max = Stdlib.max
  let min = Stdlib.min
end

let clamp x lo hi =
  let lo' = Z.min lo hi in
  let hi' = Z.max lo hi in
  if Z.ltb x lo' then lo' else if Z.gtb x hi' then hi' else x

(* Runtime bounds check - extracted from Coq with correctness proof *)
let check_bounds min max z =
  Z.leb min z && Z.leb z max

(* Safe clamp: validates bounds at runtime, returns option *)
let clamp_safe ~min ~max x lo hi =
  if check_bounds min max lo && check_bounds min max hi then
    let result = clamp x lo hi in
    (* Coq proves: check_bounds min max result = true *)
    Some result
  else
    None

(* === Basic Tests === *)
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

  print_endline "Basic tests passed!"

(* === Runtime Bounds Validation Tests === *)
let () =
  (* check_bounds correctness *)
  assert (check_bounds 0 100 50 = true);
  assert (check_bounds 0 100 0 = true);
  assert (check_bounds 0 100 100 = true);
  assert (check_bounds 0 100 (-1) = false);
  assert (check_bounds 0 100 101 = false);

  (* clamp_safe with valid bounds *)
  assert (clamp_safe ~min:0 ~max:100 50 10 90 = Some 50);
  assert (clamp_safe ~min:0 ~max:100 5 10 90 = Some 10);
  assert (clamp_safe ~min:0 ~max:100 95 10 90 = Some 90);

  (* clamp_safe with out-of-range bounds - rejects *)
  assert (clamp_safe ~min:0 ~max:100 50 (-10) 90 = None);
  assert (clamp_safe ~min:0 ~max:100 50 10 110 = None);

  (* The guarantee: if clamp_safe returns Some v, then check_bounds v = true *)
  let test_guarantee min max x lo hi =
    match clamp_safe ~min ~max x lo hi with
    | None -> () (* bounds invalid, correctly rejected *)
    | Some v -> assert (check_bounds min max v = true)
  in
  test_guarantee 0 100 50 10 90;
  test_guarantee 0 100 5 10 90;
  test_guarantee 0 100 200 10 90;
  test_guarantee (-50) 50 0 (-10) 10;

  print_endline "Runtime bounds validation tests passed!"

(* === Overflow Safety Demonstration === *)
let () =
  (* Simulate int63 bounds *)
  let int63_min = -(1 lsl 62) in
  let int63_max = (1 lsl 62) - 1 in

  (* If bounds are valid int63, result is valid int63 *)
  let safe_result = clamp_safe ~min:int63_min ~max:int63_max
    999999999999 0 1000000000000 in
  (match safe_result with
   | Some v -> assert (check_bounds int63_min int63_max v = true)
   | None -> failwith "bounds should be valid");

  print_endline "Overflow safety tests passed!"

let () =
  print_endline "All tests passed!"
