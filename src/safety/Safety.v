(* ================================================================== *)
(* Safety: re-export shim.                                            *)
(*                                                                    *)
(* The progress/preservation/soundness metatheory was split into      *)
(* dependency-ordered modules (see _CoqProject); this shim re-exports  *)
(* them so downstream files keep `Require Import Safety`.              *)
(* ================================================================== *)
Require Export SafetyMarkers.
Require Export SafetyProgress.
Require Export SafetyElim1.
Require Export SafetyElim2.
Require Export SafetyConfinement.
Require Export SafetyPreservation.
