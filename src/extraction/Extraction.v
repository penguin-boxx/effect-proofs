From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.
Require Import Syntax.
Require Import Stepf.
Require Import Decide.
Require Import Examples.

(* ================================================================== *)
(* OCaml extraction of the computational layer.                       *)
(*                                                                    *)
(* Everything extracted here is a pure computable definition whose    *)
(* specification is a gated theorem:                                  *)
(*                                                                    *)
(*   stepf / stepf_run   the certified evaluator and its bounded      *)
(*                       driver (stepf_sound, stepf_run_sound,        *)
(*                       stepf_complete_modulo_markers,               *)
(*                       stepf_classification);                       *)
(*   lt_subb / nolocb /  the reflected deciders (lt_subb_spec,        *)
(*   valueb / sourceb    nolocb_spec, valueb_spec, sourceb_spec);     *)
(*                                                                    *)
(* plus a few example programs and expected values for the smoke      *)
(* driver (main.ml).  The fresh-marker choice needs no OCaml-side     *)
(* generator: [stepf] allocates [marker_bound t] internally, the      *)
(* same canonical witness the soundness proof uses.                   *)
(*                                                                    *)
(* [ExtrOcamlBasic] maps bool/option/list/prod onto their OCaml       *)
(* counterparts; [nat] is deliberately left as the Peano inductive —  *)
(* no numeric overflow can be smuggled in by the extraction.          *)
(*                                                                    *)
(* The generated evaluator.ml/.mli are build products (gitignored);   *)
(* `make extract-run` compiles them with the hand-written main.ml     *)
(* smoke driver and runs it.  Optional — nothing in `make verify`     *)
(* depends on the OCaml toolchain.                                    *)
(* ================================================================== *)

Set Extraction Output Directory "extraction".

Extraction "evaluator.ml"
  stepf stepf_run
  lt_subb nolocb valueb sourceb
  reader_example state_sum_example chan_example
  two_v five_v.
