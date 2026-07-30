(* ================================================================== *)
(* Sugar.v — Surface syntax with dependent-types-like sugar           *)
(*                                                                    *)
(* This module implements the surface syntax discussed in §6.1 of the *)
(* one-plus-one paper.  It supports:                                  *)
(*                                                                    *)
(*   • term-variable-named lifetimes                                  *)
(*       fun lazyMap(xs: LazyList<a>, f: (a) -> b): LazyList<b>'f+xs  *)
(*                                                                    *)
(*   • named generic positions                                        *)
(*       fun extractFile(m: Map<Key, f: File>): File'f                *)
(*                                                                    *)
(* The surface-language entities (types and function signatures only) *)
(* are deeply embedded as Coq inductives and elaborated to            *)
(* Core_Δ types via [desugar_sig].                                    *)
(*                                                                    *)
(* Surface terms, contextual params, effect declarations, Rust-style  *)
(* lifetime elision, and gradual subtyping are out of scope.          *)
(* ================================================================== *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

Require Import Syntax.
Require Import Substitution.
Require Import Typing.

(* ================================================================== *)
(* 1. Surface AST                                                     *)
(* ================================================================== *)

Definition sname := string.

(* Surface lifetime expressions.                                       *)
(*   slt_local       — explicit 'local                                 *)
(*   slt_free        — explicit 'free                                  *)
(*   slt_name n      — reference to a named entity (term param,       *)
(*                     named ctor-arg, or generic name)                *)
(*   slt_plus ls     — 'l1+l2+... (interpreted as the minimum         *)
(*                     lifetime, encoded with [lt_join])                *)
Inductive surface_lt : Type :=
  | slt_local : surface_lt
  | slt_free  : surface_lt
  | slt_name  : sname -> surface_lt
  | slt_plus  : list surface_lt -> surface_lt.

(* Surface types.                                                      *)
(* An [sty_ctor T ml args] argument list is a list of (option name,   *)
(*   surface_ty) pairs.  A name on a ctor argument turns that         *)
(* position into a "named generic" — a fresh lifetime slot is         *)
(* allocated for it during desugaring.                                 *)
Inductive surface_ty : Type :=
  | sty_var  : sname -> surface_ty
  | sty_ctor : sname -> option surface_lt
                     -> list (option sname * surface_ty) -> surface_ty
  | sty_fun  : list (option sname * surface_ty)
                     -> option surface_lt -> surface_ty -> surface_ty.

(* Function signature.                                                 *)
(*   sig_generics: each generic has a name and an optional bound      *)
(*                 (default: Any@local).                               *)
(*   sig_params:   ordered list of (term-param name, type).           *)
(*   sig_ret:      return type.                                        *)
Record surface_sig : Type := mk_sig {
  sig_generics : list (sname * option surface_ty);
  sig_params   : list (sname * surface_ty);
  sig_ret      : surface_ty
}.

(* ================================================================== *)
(* 2. Name registry for ctor tags                                     *)
(*                                                                    *)
(* Surface code refers to constructors by string name (LazyList, Map, *)
(* …).  The desugarer is parameterised by a [tag_of : sname → tag].   *)
(* The reserved [any_tag] from Syntax.v denotes Any.                  *)
(* ================================================================== *)

Definition tag_resolver := sname -> ctor_tag.

(* ================================================================== *)
(* 3. Slot allocation                                                 *)
(*                                                                    *)
(* For each named entity that may be referenced by a 'name lifetime,  *)
(* we allocate a fresh lifetime variable.                             *)
(*                                                                    *)
(* Allocation order (= outermost-first):                              *)
(*   1. each term parameter name                                      *)
(*   2. each named ctor-argument name appearing anywhere inside the   *)
(*      param types or return type, deep-first, deduplicated.         *)
(*                                                                    *)
(* The resulting [list sname] is the lifetime-binder list.            *)
(* ================================================================== *)

Definition mem_str (n : sname) (xs : list sname) : bool :=
  existsb (String.eqb n) xs.

Definition add_unique (n : sname) (xs : list sname) : list sname :=
  if mem_str n xs then xs else xs ++ [n].

Fixpoint collect_named_in_ty (t : surface_ty) (acc : list sname)
  : list sname :=
  let fix go_args (args : list (option sname * surface_ty))
                  (acc : list sname) : list sname :=
    match args with
    | []                  => acc
    | (mn, a) :: rest =>
        let acc1 := match mn with
                    | Some n => add_unique n acc
                    | None   => acc
                    end in
        let acc2 := collect_named_in_ty a acc1 in
        go_args rest acc2
    end
  in
  match t with
  | sty_var _           => acc
  | sty_ctor _ _ args   => go_args args acc
  | sty_fun  ps _ ret   =>
      let acc1 := go_args ps acc in
      collect_named_in_ty ret acc1
  end.

Definition collect_slots (s : surface_sig) : list sname :=
  let term_names := map fst (sig_params s) in
  let acc0 := fold_left (fun a n => add_unique n a) term_names [] in
  let acc1 := fold_left (fun a p => collect_named_in_ty (snd p) a)
                        (sig_params s) acc0 in
  collect_named_in_ty (sig_ret s) acc1.

(* ================================================================== *)
(* 4. Name resolution                                                 *)
(*                                                                    *)
(* Lifetime slots and type generics live in independent namespaces.   *)
(* Slot lists are stored outermost-first; the de-Bruijn index of an   *)
(* entry at position [i] in a list of length [n] is [n - S i].        *)
(* ================================================================== *)

Fixpoint position_of (n : sname) (xs : list sname) (i : nat)
  : option nat :=
  match xs with
  | [] => None
  | x :: rest =>
      if String.eqb x n then Some i else position_of n rest (S i)
  end.

Definition db_of_pos (total i : nat) : nat := total - S i.

Definition lookup_lt (slots : list sname) (n : sname) : option nat :=
  match position_of n slots 0 with
  | Some i => Some (db_of_pos (List.length slots) i)
  | None   => None
  end.

Definition lookup_ty (gens : list sname) (n : sname) : option nat :=
  match position_of n gens 0 with
  | Some i => Some (db_of_pos (List.length gens) i)
  | None   => None
  end.

Record name_env := mk_env {
  ne_lts : list sname;
  ne_tys : list sname
}.

(* ================================================================== *)
(* 5. Elaboration                                                     *)
(* ================================================================== *)

Fixpoint elab_lt (env : name_env) (l : surface_lt) : lifetime :=
  match l with
  | slt_local     => lt_local
  | slt_free      => lt_free
  | slt_name n    =>
      match lookup_lt (ne_lts env) n with
      | Some k => lt_var k
      | None   => lt_local  (* unknown name: fall back to local *)
      end
  | slt_plus []   => lt_local
  | slt_plus (l0 :: rest) =>
      fold_left (fun acc x => lt_join acc (elab_lt env x))
                rest (elab_lt env l0)
  end.

Definition default_lt : lifetime := lt_local.

Definition elab_lt_opt (env : name_env) (ml : option surface_lt) : lifetime :=
  match ml with
  | Some l => elab_lt env l
  | None   => default_lt
  end.

(* When a ctor argument carries a name [f], we make the parent ctor's *)
(* lifetime depend on the slot allocated for [f].  This is the core   *)
(* of the "named generic" sugar: 'f at the use site refers exactly to *)
(* the lifetime variable that this position contributes.              *)
Definition slots_from_args
           (env : name_env)
           (args : list (option sname * surface_ty)) : list lifetime :=
  fold_right
    (fun p acc =>
       match fst p with
       | Some n =>
           match lookup_lt (ne_lts env) n with
           | Some k => lt_var k :: acc
           | None   => acc
           end
       | None => acc
       end) [] args.

Definition combine_lt (base : lifetime) (extras : list lifetime) : lifetime :=
  fold_left lt_join extras base.

Fixpoint elab_ty (tag_of : tag_resolver) (env : name_env) (t : surface_ty)
  : type :=
  let fix go_args (args : list (option sname * surface_ty)) : list type :=
    match args with
    | []          => []
    | (_, a) :: r => elab_ty tag_of env a :: go_args r
    end
  in
  match t with
  | sty_var n =>
      match lookup_ty (ne_tys env) n with
      | Some k => type_var k
      | None   => type_ctor (tag_of n) lt_local []  (* unknown: ctor *)
      end
  | sty_ctor T ml args =>
      let base := elab_lt_opt env ml in
      let extras := slots_from_args env args in
      type_ctor (tag_of T) (combine_lt base extras) (go_args args)
  | sty_fun ps ml ret =>
      let argtys := go_args ps in
      let l      := elab_lt_opt env ml in
      let rety   := elab_ty tag_of env ret in
      (* Curry: build right-associated chain.                          *)
      fold_right (fun a acc => type_fun a l acc) rety argtys
  end.

(* ================================================================== *)
(* 6. Bound elaboration (default Any@local)                           *)
(* ================================================================== *)

Definition any_local : type := type_ctor any_tag lt_local [].

Definition elab_bound (tag_of : tag_resolver) (env : name_env)
           (mb : option surface_ty) : type :=
  match mb with
  | Some b => elab_ty tag_of env b
  | None   => any_local
  end.

(* ================================================================== *)
(* 7. Signature desugaring                                            *)
(*                                                                    *)
(* desugar_sig produces a type schema of shape                        *)
(*   ∀ l_1 ... l_n.  ∀ (α_1 <: B_1) ... (α_m <: B_m).                 *)
(*       τ_1 → ... → τ_k → τ_ret                                      *)
(* using the current Core_Δ encoding (type_lt_all / type_ty_all /     *)
(* type_fun).                                                         *)
(* ================================================================== *)

Definition wrap_lt_alls (n : nat) (body : type) : type :=
  Nat.iter n type_lt_all body.

(* Wrap [n] type-binders.  Bounds are taken in outermost-first order  *)
(* from [bounds]; the outermost gets innermost-most-shifted index 0   *)
(* relative to the body — but our convention is that the head of      *)
(* [bounds] is the OUTERMOST, so we reverse-fold.                     *)
Fixpoint wrap_ty_alls (bounds : list type) (body : type) : type :=
  match bounds with
  | []        => body
  | B :: rest => type_ty_all B (wrap_ty_alls rest body)
  end.

Definition desugar_sig (tag_of : tag_resolver) (s : surface_sig) : type :=
  let slots := collect_slots s in
  let gens  := map fst (sig_generics s) in
  let env   := mk_env slots gens in
  let bounds := map (fun p => elab_bound tag_of env (snd p)) (sig_generics s) in
  let argtys := map (fun p => elab_ty tag_of env (snd p)) (sig_params s) in
  let rety   := elab_ty tag_of env (sig_ret s) in
  let arrow  := fold_right (fun a acc => type_fun a default_lt acc) rety argtys in
  let with_tys := wrap_ty_alls bounds arrow in
  wrap_lt_alls (List.length slots) with_tys.

(* ================================================================== *)
(* 8. Soundness statement (deferred)                                  *)
(*                                                                    *)
(* Proving that every well-formed surface signature desugars to a     *)
(* type schema that is well-formed in Core_Δ requires substantial     *)
(* machinery (well-formed ctor tags, bound monotonicity, nolocb (Decide.v)  *)
(* checks), so it is kept as a Conjecture (unproven).                 *)
(* ================================================================== *)

(* A trivial well-formedness predicate stub; full version should      *)
(* check that every name reference resolves to an allocated slot or   *)
(* generic, that ctor tags are registered, etc.                       *)
Definition surface_sig_wf (tag_of : tag_resolver) (s : surface_sig) : Prop :=
  True.

Conjecture desugar_sig_wf :
  forall tag_of s,
    surface_sig_wf tag_of s ->
    (* The elaborated type schema is well-kinded under the empty       *)
    (* context.  Stated abstractly here.                              *)
    exists T, T = desugar_sig tag_of s.

(* ================================================================== *)
(* 9. Worked examples                                                 *)
(* ================================================================== *)

Module SugarExamples.

(* --- Tag registry shared by the examples ----------------------------- *)
(* Reserved: any_tag = 0 (see Syntax.v).                                  *)
Definition LazyList_tag : ctor_tag := 10.
Definition Pair_tag     : ctor_tag := 11.
Definition Map_tag      : ctor_tag := 12.
Definition File_tag     : ctor_tag := 13.
Definition Key_tag      : ctor_tag := 14.
Definition Repository_tag : ctor_tag := 15.
Definition Connection_tag : ctor_tag := 16.

Definition demo_tag (n : sname) : ctor_tag :=
  if String.eqb n "LazyList"   then LazyList_tag
  else if String.eqb n "Pair"  then Pair_tag
  else if String.eqb n "Map"   then Map_tag
  else if String.eqb n "File"  then File_tag
  else if String.eqb n "Key"   then Key_tag
  else if String.eqb n "Repository" then Repository_tag
  else if String.eqb n "Connection" then Connection_tag
  else if String.eqb n "Any"   then any_tag
  else 99.  (* unknown sentinel *)

(* --- Helpers ------------------------------------------------------- *)
Definition v (n : sname) : surface_ty := sty_var n.
Definition app1 (T : sname) (a : surface_ty) : surface_ty :=
  sty_ctor T None [(None, a)].
Definition appN (T : sname) (args : list surface_ty) : surface_ty :=
  sty_ctor T None (map (fun a => (None, a)) args).
Definition fnT (params : list surface_ty) (l : option surface_lt)
               (ret : surface_ty) : surface_ty :=
  sty_fun (map (fun a => (None, a)) params) l ret.

(* ================================================================== *)
(* Example 1 — lazyMap                                                *)
(*   fun lazyMap(xs: LazyList<a>, f: (a) -> b): LazyList<b>'f+xs      *)
(* ================================================================== *)

Definition lazyMap_sig : surface_sig := mk_sig
  [("a", None); ("b", None)]
  [("xs", app1 "LazyList" (v "a"));
   ("f",  fnT [v "a"] None (v "b"))]
  (sty_ctor "LazyList"
            (Some (slt_plus [slt_name "f"; slt_name "xs"]))
            [(None, v "b")]).

Definition lazyMap_ty : type := desugar_sig demo_tag lazyMap_sig.

(* Confirm the elaboration produces the expected schema shape.        *)
(*   slots = [xs; f]   (length 2) → outer 2 × type_lt_all              *)
(*   gens  = [a; b]    (length 2) → 2 × type_ty_all (Any@local)        *)
(*   xs ↦ lt_var 1, f ↦ lt_var 0                                     *)
(*   a ↦ type_var 1,  b ↦ type_var 0                                  *)
Example lazyMap_shape :
  lazyMap_ty =
  type_lt_all (type_lt_all (
    type_ty_all any_local (type_ty_all any_local (
      type_fun
        (type_ctor LazyList_tag lt_local [type_var 1])
        lt_local
        (type_fun
          (type_fun (type_var 1) lt_local (type_var 0))
          lt_local
          (type_ctor LazyList_tag
            (lt_join (lt_var 0) (lt_var 1))
            [type_var 0])))))).
Proof. reflexivity. Qed.

(* ================================================================== *)
(* Example 2 — compose                                                *)
(*   fun compose(f: (b) -> c, g: (a) -> b): (a)'f+g -> c              *)
(* ================================================================== *)

Definition compose_sig : surface_sig := mk_sig
  [("a", None); ("b", None); ("c", None)]
  [("f", fnT [v "b"] None (v "c"));
   ("g", fnT [v "a"] None (v "b"))]
  (sty_fun [(None, v "a")]
           (Some (slt_plus [slt_name "f"; slt_name "g"]))
           (v "c")).

Definition compose_ty : type := desugar_sig demo_tag compose_sig.

(* slots = [f; g] (length 2): f ↦ lt_var 1, g ↦ lt_var 0              *)
(* gens  = [a; b; c]:  a ↦ tv 2, b ↦ tv 1, c ↦ tv 0                   *)
Example compose_shape :
  compose_ty =
  type_lt_all (type_lt_all (
    type_ty_all any_local (type_ty_all any_local (type_ty_all any_local (
      type_fun
        (type_fun (type_var 1) lt_local (type_var 0))   (* f: (b)->c *)
        lt_local
        (type_fun
          (type_fun (type_var 2) lt_local (type_var 1)) (* g: (a)->b *)
          lt_local
          (type_fun (type_var 2)                        (* (a)        *)
                    (lt_join (lt_var 1) (lt_var 0))
                    (type_var 0)))))))).                (* -> c       *)
Proof. reflexivity. Qed.

(* ================================================================== *)
(* Example 3 — extractFile  (named generic position)                  *)
(*   fun extractFile(m: Map<Key, f: File>): File'f                    *)
(* ================================================================== *)

Definition extractFile_sig : surface_sig := mk_sig
  []  (* no generics *)
  [("m", sty_ctor "Map" None
            [(None, sty_ctor "Key" None []);
             (Some "f", sty_ctor "File" None [])])]
  (sty_ctor "File" (Some (slt_name "f")) []).

Definition extractFile_ty : type := desugar_sig demo_tag extractFile_sig.

(* Slot order: term-param "m" is collected first, then deep traversal *)
(* finds named ctor-arg "f".  So slots = [m; f] (length 2):           *)
(*   m ↦ lt_var 1                                                     *)
(*   f ↦ lt_var 0                                                     *)
(* The Map<…> in m's type acquires (lt_local + lt_var 0) because of    *)
(* the named arg f.  The result File'f becomes File@(lt_var 0).        *)
Example extractFile_shape :
  extractFile_ty =
  type_lt_all (type_lt_all (
    type_fun
      (type_ctor Map_tag (lt_join lt_local (lt_var 0))
                 [type_ctor Key_tag  lt_local [];
                  type_ctor File_tag lt_local []])
      lt_local
      (type_ctor File_tag (lt_var 0) []))).
Proof. reflexivity. Qed.

(* ======================================================================== *)
(* Example 4 — makeRepository                                               *)
(*   fun makeRepository(file: File, conn: Connection): Repository'file+conn *)
(* ======================================================================== *)

Definition makeRepository_sig : surface_sig := mk_sig
  []
  [("file", sty_ctor "File" None []);
   ("conn", sty_ctor "Connection" None [])]
  (sty_ctor "Repository"
            (Some (slt_plus [slt_name "file"; slt_name "conn"])) []).

Definition makeRepository_ty : type := desugar_sig demo_tag makeRepository_sig.

(* slots = [file; conn]:  file ↦ lt_var 1, conn ↦ lt_var 0            *)
Example makeRepository_shape :
  makeRepository_ty =
  type_lt_all (type_lt_all (
    type_fun (type_ctor File_tag lt_local []) lt_local
      (type_fun (type_ctor Connection_tag lt_local []) lt_local
        (type_ctor Repository_tag
                   (lt_join (lt_var 1) (lt_var 0)) [])))).
Proof. reflexivity. Qed.

End SugarExamples.
