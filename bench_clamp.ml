(* Benchmark: extracted clamp vs handwritten *)

open Clamp

let clamp_handwritten x lo hi =
  if x < lo then lo else if x > hi then hi else x

let time_it name f n =
  let t0 = Sys.time () in
  for _ = 1 to n do
    ignore (f ())
  done;
  let t1 = Sys.time () in
  Printf.printf "%s: %.4f sec (%d iterations)\n" name (t1 -. t0) n

let () =
  let n = 10_000_000 in

  time_it "extracted clamp" (fun () -> clamp 50 0 100) n;
  time_it "handwritten clamp" (fun () -> clamp_handwritten 50 0 100) n;

  time_it "extracted (below)" (fun () -> clamp (-10) 0 100) n;
  time_it "handwritten (below)" (fun () -> clamp_handwritten (-10) 0 100) n;

  time_it "extracted (above)" (fun () -> clamp 150 0 100) n;
  time_it "handwritten (above)" (fun () -> clamp_handwritten 150 0 100) n;

  print_endline "Benchmark complete."
