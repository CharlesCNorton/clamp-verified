(* Tests for clamp.ml extracted from Clamp.v *)

open Clamp

(* === Basic Tests === *)
let () =
  assert (clamp 5 0 10 = 5);
  assert (clamp (-5) 0 10 = 0);
  assert (clamp 15 0 10 = 10);

  assert (clamp 0 0 10 = 0);
  assert (clamp 10 0 10 = 10);

  assert (clamp 5 10 0 = 5);
  assert (clamp (-5) 10 0 = 0);
  assert (clamp 15 10 0 = 10);

  assert (clamp (clamp 5 0 10) 0 10 = clamp 5 0 10);
  assert (clamp (clamp (-5) 0 10) 0 10 = clamp (-5) 0 10);
  assert (clamp (clamp 15 0 10) 0 10 = clamp 15 0 10);
  assert (clamp (clamp 5 10 0) 10 0 = clamp 5 10 0);

  assert (clamp 5 5 5 = 5);
  assert (clamp 0 5 5 = 5);
  assert (clamp 10 5 5 = 5);

  print_endline "Basic tests passed!"

(* === clamp_safe Tests === *)
let () =
  assert (clamp_safe 5 0 10 = Some 5);
  assert (clamp_safe (-5) 0 10 = Some 0);
  assert (clamp_safe 15 0 10 = Some 10);

  assert (clamp_safe 5 10 0 = None);

  print_endline "clamp_safe tests passed!"

(* === clamp_list Tests === *)
let () =
  assert (clamp_list [1; 5; 15; (-5)] 0 10 = [1; 5; 10; 0]);
  assert (clamp_list [] 0 10 = []);
  assert (clamp_list [5] 5 5 = [5]);

  print_endline "clamp_list tests passed!"

(* === check_bounds Tests === *)
let () =
  assert (check_bounds 0 100 50 = true);
  assert (check_bounds 0 100 0 = true);
  assert (check_bounds 0 100 100 = true);
  assert (check_bounds 0 100 (-1) = false);
  assert (check_bounds 0 100 101 = false);

  print_endline "check_bounds tests passed!"

(* === clamp_checked Tests === *)
let () =
  let (result, valid) = clamp_checked 0 100 50 10 90 in
  assert (result = 50);
  assert (valid = true);

  let (result, valid) = clamp_checked 0 100 5 10 90 in
  assert (result = 10);
  assert (valid = true);

  let (result, valid) = clamp_checked 0 100 50 (-10) 90 in
  assert (valid = false);

  print_endline "clamp_checked tests passed!"

(* === Int63 Specialization Tests === *)
let () =
  assert (check_int63_bounds 0 = true);
  assert (check_int63_bounds 1000000000000 = true);
  assert (check_int63_bounds (-1000000000000) = true);

  let (result, valid) = clamp_int63_checked 50 0 100 in
  assert (result = 50);
  assert (valid = true);

  print_endline "Int63 tests passed!"

(* === All Tests Complete === *)
let () =
  print_endline "All extracted code tests passed!"
