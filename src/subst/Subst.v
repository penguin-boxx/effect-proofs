(* ================================================================== *)
(* Subst: re-export shim.                                *)
(*                                                                    *)
(* The substitution metatheory was split into seven dependency-       *)
(* ordered modules (see _CoqProject).  This shim re-exports them so   *)
(* downstream files can keep `Require Import Subst`.      *)
(* ================================================================== *)
Require Export ShiftLaws.
Require Export Insertions.
Require Export SubstLt.
Require Export SubstTy.
Require Export SubstTm.
Require Export EvalCtx.
Require Export TypingSubstTy.
