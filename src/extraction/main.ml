(* Smoke driver for the extracted evaluator (see Extraction.v).
   Each check re-runs, in OCaml, a fact that is also a gated theorem
   on the Rocq side — the point is that the EXTRACTED code computes
   the same answers, end to end, outside the prover. *)

open Evaluator

let rec nat_of_int n = if n <= 0 then O else S (nat_of_int (n - 1))

let fuel = nat_of_int 100

let failed = ref false

let check name ok =
  Printf.printf "%-42s %s\n" name (if ok then "OK" else "FAIL");
  if not ok then failed := true

let () =
  (* red_reader_example: handle { ask() resume(2) } perform ask() ~>* 2 *)
  check "reader_example runs to 2"
    (stepf_run fuel reader_example = two_v);
  (* red_state_sum_example: the state-passing run computes 2+3 = 5 *)
  check "state_sum_example runs to 5"
    (stepf_run fuel state_sum_example = five_v);
  (* red_chan_example reaches a value (multi-op, beta-polymorphic) *)
  check "chan_example reaches a value"
    (valueb (stepf_run fuel chan_example));
  (* stepf_value_none: values do not step *)
  check "values do not step"
    (stepf two_v = None);
  (* sourceb_spec: the example programs are source terms *)
  check "sourceb accepts the source programs"
    (sourceb reader_example && sourceb state_sum_example
     && sourceb chan_example);
  if !failed then exit 1
