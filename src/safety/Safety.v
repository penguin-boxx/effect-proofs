(* ================================================================== *)
(* Safety: re-export shim.                                            *)
(*                                                                    *)
(* The progress/preservation/soundness metatheory was split into      *)
(* dependency-ordered modules (see _CoqProject); this shim re-exports  *)
(* them so downstream files keep `Require Import Safety`.              *)
(* ================================================================== *)
Require Export Markers.
Require Export Progress.
Require Export Variance.
Require Export Inversions.
Require Export Frames.
Require Export Preservation.
Require Export Soundness.
Require Export Escape.
