(* ================================================================== *)
(* SubstitutionTheory: re-export shim.                                *)
(*                                                                    *)
(* The substitution metatheory was split into seven dependency-       *)
(* ordered modules (see _CoqProject).  This shim re-exports them so   *)
(* downstream files can keep `Require Import SubstitutionTheory`.      *)
(* ================================================================== *)
Require Export STShiftLaws.
Require Export STInsertions.
Require Export STSubstLt.
Require Export STSubstTy.
Require Export STSubstTm.
Require Export STEvalCtx.
Require Export STTypingSubstTy.
