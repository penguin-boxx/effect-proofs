(* ================================================================== *)
(* Subst: re-export shim for the substitution tier.                   *)
(*                                                                    *)
(* The substitution metatheory is split into dependency-ordered       *)
(* modules (see _CoqProject).  This shim re-exports them so           *)
(* downstream files can `Require Import Subst`.  Narrowing and        *)
(* Variance are also part of this tier but come AFTER the shim in     *)
(* build order (Variance itself imports Subst); files needing them    *)
(* import them directly.                                              *)
(* ================================================================== *)
Require Export SubstTactics.
Require Export ShiftLaws.
Require Export Weakening.
Require Export SubstLt.
Require Export SubstTy.
Require Export ProgramCtx.
Require Export SubstTm.
Require Export TypingSubst.
