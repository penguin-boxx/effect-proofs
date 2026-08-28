Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.

(* ================================================================== *)
(* Core examples: definitions and statements only.                    *)
(*                                                                    *)
(* Naming: every example program is <subject>_example; the subject    *)
(* itself may be camelCase when it names a program from the paper     *)
(* (withFile, mapFirst, foldEndo, ...) — deliberate, do not "fix".    *)
(*                                                                    *)
(* Placement discipline for this file: each example's typing and      *)
(* reduction statements (typed_*/red_*, as Prop definitions) sit      *)
(* directly after the example's own definition block; the negative    *)
(* statements form their own section at the end of the file.          *)
(*                                                                    *)
(* Proofs of these statements live in ExamplesProofs.v.               *)
(* ================================================================== *)

Module CoreNotation.
  Notation "'`Lf'"     := lt_free.
  Notation "'`Ll'"     := lt_local.
  Notation "'`L' n"    := (lt_var n) (at level 5, format "'`L'  n").
  Notation "l1 '+l' l2" := (lt_join l1 l2) (at level 50, left associativity).

  Notation "'`T' n" := (type_var n) (at level 5, format "'`T'  n").
  Notation "A '-{' l '}->' B" :=
    (type_fun A l B) (at level 70, right associativity, l at level 0).
  Notation "'$$' n" := (term_var n) (at level 5, format "'$$' n").
  Notation "t '@·' u" := (term_app t u) (at level 31, left associativity).
  Notation "'λ:' T '\\' body" :=
    (term_lam body T)
    (at level 80, T at level 0, body at level 80, right associativity).
  Notation "'Λl' '\\' body" :=
    (term_lt_lam body) (at level 80, body at level 80, right associativity).
  Notation "'Λt:' B '\\' body" :=
    (term_ty_lam B body)
    (at level 80, B at level 0, body at level 80, right associativity).
  Notation "t '@ty[' T ']'" := (term_ty_app t T) (at level 31, left associativity).
  Notation "t '@lt[' l ']'" := (term_lt_app t l) (at level 31, left associativity).
  Notation "'let:' T '<-' e 'in' body" :=
    (term_app (term_lam body T) e)
    (at level 80, T at level 0, e at level 80, body at level 80,
     right associativity).
End CoreNotation.

Import CoreNotation.

Notation "t '==>>' t'" := (multi_step t t') (at level 40).

(* ================================================================== *)
(* 1. Data declarations                                               *)
(* ================================================================== *)

Definition unit_tag : ctor_tag := 10.

Definition option_tag : ctor_tag := 20.
Definition none_tag   : ctor_tag := 21.
Definition some_tag   : ctor_tag := 22.

Definition result_tag : ctor_tag := 30.
Definition error_tag  : ctor_tag := 31.
Definition ok_tag     : ctor_tag := 32.

Definition file_tag : ctor_tag := 40.

Definition list_tag : ctor_tag := 50.
Definition nil_tag  : ctor_tag := 51.
Definition cons_tag : ctor_tag := 52.

Definition nat_tag  : ctor_tag := 60.
Definition zero_tag : ctor_tag := 61.
Definition suc_tag  : ctor_tag := 62.

Definition lazy_list_tag  : ctor_tag := 70.
Definition lnil_tag       : ctor_tag := 71.
Definition lcons_tag      : ctor_tag := 72.

Definition pair_tag : ctor_tag := 80.

Definition endoi_tag : ctor_tag := 90.
Definition endo_tag  : ctor_tag := 91.
Definition trash_tag : ctor_tag := 92.
Definition box_tag   : ctor_tag := 93.

(* Readable type abbreviations.  Each [type_ctor K l args] is the     *)
(* surface type [K<args>'l]: a data type [K] at lifetime [l]          *)
(* applied to type args.  So e.g. [T_Option `Ll A] is                 *)
(* [Option<A>'local] and [T_Nat `Lf] is [Nat'free].                   *)
Definition T_Any (l : lifetime) : type := type_ctor any_tag l [].
Definition T_Unit : type := type_ctor unit_tag `Lf [].
Definition T_Option (l : lifetime) (A : type) : type := type_ctor option_tag l [A].
Definition T_Result (l : lifetime) (E A : type) : type := type_ctor result_tag l [E; A].
Definition T_File (l : lifetime) : type := type_ctor file_tag l [].
Definition T_List (l : lifetime) (A : type) : type := type_ctor list_tag l [A].
Definition T_Nat (l : lifetime) : type := type_ctor nat_tag l [].
Definition T_LazyList (l : lifetime) (A : type) : type := type_ctor lazy_list_tag l [A].
Definition T_Pair (l : lifetime) (A B : type) : type := type_ctor pair_tag l [A; B].
Definition T_EndoI (l : lifetime) : type := type_ctor endoi_tag l [].
Definition T_Endo (l : lifetime) (A : type) : type := type_ctor endo_tag l [A].
Definition T_Trash (l : lifetime) : type := type_ctor trash_tag l [].
Definition T_Box (l : lifetime) : type := type_ctor box_tag l [].

(* data Unit = Unit *)
Definition unit_sig : binding := bind_ctor unit_tag 0 0 [] T_Unit.

(* data Option<a> = None | Some(a) *)
Definition none_sig : binding :=
  bind_ctor none_tag 0 1 [] (T_Option `Lf (`T 0)).
Definition some_sig : binding :=
  bind_ctor some_tag 0 1 [`T 0] (T_Option `Lf (`T 0)).

(* data Result<e, a> = Error(e) | Ok(a) *)
Definition error_sig : binding :=
  bind_ctor error_tag 0 2 [`T 0] (T_Result `Lf (`T 0) (`T 1)).
Definition ok_sig : binding :=
  bind_ctor ok_tag 0 2 [`T 1] (T_Result `Lf (`T 0) (`T 1)).

(* data File = File *)
Definition file_sig : binding := bind_ctor file_tag 0 0 [] (T_File `Lf).

(* data List<a> = Nil | Cons(a, List<a>) *)
Definition nil_sig : binding :=
  bind_ctor nil_tag 0 1 [] (T_List `Lf (`T 0)).
Definition cons_sig : binding :=
  bind_ctor cons_tag 0 1 [`T 0; T_List `Lf (`T 0)] (T_List `Lf (`T 0)).

(* data Nat = Zero | Suc(Nat) *)
Definition zero_sig : binding := bind_ctor zero_tag 0 0 [] (T_Nat `Lf).
Definition suc_sig : binding := bind_ctor suc_tag 0 0 [T_Nat `Lf] (T_Nat `Lf).

(* data LazyList<a> =                                                         *)
(*   LNil | LCons[lr, lh, lt, ll](()'lh -> a, ()'lt -> LazyList<a>'ll)        *)
(*           : LazyList<a>'lr                                                 *)
Definition lnil_sig : binding :=
  bind_ctor lnil_tag 0 1 [] (T_LazyList `Lf (`T 0)).
Definition lcons_sig : binding :=
  bind_ctor lcons_tag 4 1
    [ T_Unit -{ `L 2 }-> `T 0
    ; T_Unit -{ `L 1 }-> T_LazyList (`L 0) (`T 0) ]
    (T_LazyList (`L 3) (`T 0)).

(* data Pair<a, b> = Pair(a, b) *)
Definition pair_sig : binding :=
  bind_ctor pair_tag 0 2 [`T 0; `T 1] (T_Pair `Lf (`T 0) (`T 1)).

(* data EndoI = EndoI[l]((Nat'l) -> Nat'l) *)
Definition endoi_sig : binding :=
  bind_ctor endoi_tag 1 0 [T_Nat (`L 0) -{ `Lf }-> T_Nat (`L 0)] (T_EndoI (`L 0)).

(* data Endo<a> = Endo((a) -> a) *)
Definition endo_sig : binding :=
  bind_ctor endo_tag 0 1 [`T 0 -{ `Lf }-> `T 0] (T_Endo `Lf (`T 0)).

(* data Trash = Trash[l](Endo<Nat'l>) — the field is the subject of   *)
(* the [rejected_crashEndo] variance witness below.                   *)
Definition trash_field : type := T_Endo (`L 0) (T_Nat (`L 0)).
Definition trash_sig : binding :=
  bind_ctor trash_tag 1 0 [trash_field] (T_Trash (`L 0)).

(* data Box = Box[l](Option<Nat'l>) — the field is the subject of the *)
(* [rejected_crashBox] no-local witness below.                        *)
Definition box_field : type := T_Option (`L 0) (T_Nat (`L 0)).
Definition box_sig : binding :=
  bind_ctor box_tag 1 0 [box_field] (T_Box (`L 0)).

(* [data_ctx]: the typing context holding every data-constructor      *)
(* signature above (the program's data declarations).  Used to        *)
(* type the pure examples.                                            *)
Definition data_ctx : ctx :=
  [ box_sig; trash_sig; endo_sig; endoi_sig; pair_sig; lcons_sig; lnil_sig
  ; suc_sig; zero_sig; cons_sig; nil_sig; file_sig; ok_sig; error_sig
  ; some_sig; none_sig; unit_sig ].

(* ================================================================== *)
(* 2. Effects                                                         *)
(* ================================================================== *)

Definition Reader_tag      : eff_tag := 100.
Definition Exception_tag   : eff_tag := 102.
Definition Id_tag          : eff_tag := 103.
Definition Optionality_tag : eff_tag := 104.

Definition T_Reader (l : lifetime) (E : type) : type := type_ctor Reader_tag l [E].
Definition T_Exception (l : lifetime) (E : type) : type := type_ctor Exception_tag l [E].
Definition T_Id (l : lifetime) : type := type_ctor Id_tag l [].

(* effect Reader<e> { op ask(): e } *)
Definition reader_sig : binding := bind_eff Reader_tag 1 [(0, T_Unit, `T 0)].

(* effect Exception<e> { op throw<a>(e): a } *)
Definition exception_sig : binding := bind_eff Exception_tag 1 [(1, `T 0, `T 1)].

(* effect Id { op id<a>(a): a } *)
Definition id_sig : binding := bind_eff Id_tag 0 [(1, `T 0, `T 0)].

(* effect Optionality { op mkSome<a>(a): Option<a> } *)
Definition optionality_sig : binding :=
  bind_eff Optionality_tag 0 [(1, `T 0, T_Option `Lf (`T 0))].

(* [effect_ctx]: the effect declarations.                             *)
Definition effect_ctx : ctx :=
  [ optionality_sig; id_sig; exception_sig; reader_sig ].

(* [full_ctx]: data + effects; used to type the effectful (handler)   *)
(* examples.                                                          *)
Definition full_ctx : ctx := data_ctx ++ effect_ctx.

(* ================================================================== *)
(* 3. Examples: terms with their statements                           *)
(* ================================================================== *)

(* Unit() *)
Definition unit_v : term := term_ctor unit_tag `Lf [] [] [].

(*   Unit()  :  Unit                                            *)
Definition typed_unit : Prop := data_ctx ⊢ₜ unit_v : T_Unit.

(* File() *)
Definition file_v : term := term_ctor file_tag `Lf [] [] [].

(*   File()  :  File'free                                       *)
Definition typed_file : Prop := data_ctx ⊢ₜ file_v : T_File `Lf.

(* Zero, Suc, and the numerals 2..6 (2 = Suc(Suc Zero), ...) *)
Definition zero_v : term := term_ctor zero_tag `Lf [] [] [].
Definition suc_v (n : term) : term := term_ctor suc_tag `Lf [] [] [n].
Definition two_v : term := suc_v (suc_v zero_v).
Definition three_v : term := suc_v (suc_v (suc_v zero_v)).
Definition four_v : term := suc_v three_v.
Definition five_v : term := suc_v four_v.
Definition six_v  : term := suc_v five_v.

(*   2 = Suc(Suc Zero)  :  Nat'free                             *)
Definition typed_two : Prop := data_ctx ⊢ₜ two_v : T_Nat `Lf.
(*   3 = Suc(Suc(Suc Zero))  :  Nat'free                        *)
Definition typed_three : Prop := data_ctx ⊢ₜ three_v : T_Nat `Lf.

(* fun succ(n: Nat'free): Nat'free = Suc(n)
   The successor; the calculus has no fixpoint, so "+k" is the k-fold
   composition of [succ] — see [compose_example] (which builds "+2"). *)
Definition succ_fn : term :=
  λ: T_Nat `Lf \\
    suc_v ($$ 0).

(*   succ  :  Nat -> Nat                                        *)
Definition typed_succ : Prop :=
  data_ctx ⊢ₜ succ_fn : (T_Nat `Lf -{ `Lf }-> T_Nat `Lf).

(* fun sum_k(m: Nat, n: Nat): Nat — the bounded-addition family.
   The calculus has no fixpoint, so no single term adds two arbitrary
   numerals; instead the k-th member of the family peels at most k
   Sucs off m before falling into the (for m <= k unreachable)
   default 0:
     sum_0(m, n)   = match m { Zero -> n; _ -> 0 }
     sum_k+1(m, n) = match m { Zero -> n
                             ; _ -> match m { Suc(p) -> sum_k(p, Suc(n))
                                            ; _ -> 0 } }
   For m <= k, sum_k(m, n) computes m + n.  Each member embeds the
   previous one as a literal closed subterm.                          *)
Fixpoint sum_fn (k : nat) : term :=
  match k with
  | 0 =>
      λ: T_Nat `Lf \\ λ: T_Nat `Lf \\
        term_match ($$ 1) zero_tag 0 0 ($$ 0) zero_v
  | S k' =>
      λ: T_Nat `Lf \\ λ: T_Nat `Lf \\
        term_match ($$ 1) zero_tag 0 0 ($$ 0)
          (term_match ($$ 1) suc_tag 0 1
             ((sum_fn k' @· ($$ 0)) @· suc_v ($$ 1))
             zero_v)
  end.

(* sum3 — the member wide enough for every operand in the examples.   *)
Definition sum3_fn : term := sum_fn 3.

(*   sum3  :  Nat -> Nat -> Nat                                 *)
Definition typed_sum3 : Prop :=
  data_ctx ⊢ₜ sum3_fn : (T_Nat `Lf -{ `Lf }-> T_Nat `Lf -{ `Lf }-> T_Nat `Lf).

(* sum3(2, 3) — the runnable program; [sum3_fn] itself is already   *)
(* a value, so the reduction statement is about its application.    *)
Definition sum3_example : term := (sum3_fn @· two_v) @· three_v.

(*   sum3(2, 3)  :  Nat                                         *)
Definition typed_sum3_example : Prop :=
  data_ctx ⊢ₜ sum3_example : T_Nat `Lf.

(*   sum3(2, 3)  ~~>*  5                                        *)
Definition red_sum3_example : Prop := sum3_example ==>> five_v.

(* None<a>() and Some<a>(x) *)
Definition none_v (A : type) : term := term_ctor none_tag `Lf [] [A] [].
Definition some_v (A : type) (x : term) : term :=
  term_ctor some_tag `Lf [] [A] [x].

(* Error<e,a>(e) and Ok<e,a>(a) *)
Definition error_v (E A : type) (e : term) : term :=
  term_ctor error_tag `Lf [] [E; A] [e].
Definition ok_v (E A : type) (a : term) : term :=
  term_ctor ok_tag `Lf [] [E; A] [a].

(* Nil<a>() and Cons<a>(x, xs) *)
Definition nil_v (A : type) : term := term_ctor nil_tag `Lf [] [A] [].
Definition cons_v (A : type) (x xs : term) : term :=
  term_ctor cons_tag `Lf [] [A] [x; xs].

(* Pair<a,b>(x, y) *)
Definition pair_v (A B : type) (x y : term) : term :=
  term_ctor pair_tag `Lf [] [A; B] [x; y].

(* fun withFile<r <: Any'local>(f: (File'local)'local -> r): r = f(File())
   [f]'s own arrow is LOCAL: a parameter position is contravariant, so
   demanding only a local closure is the most permissive choice — f may
   itself capture local data. *)
Definition withFile : term :=
  Λt: T_Any `Ll \\
    λ: (T_File `Ll -{ `Ll }-> `T 0) \\
      ($$ 0) @· file_v.

(*   withFile  :  <r <: Any'local>. (File'local -local-> r) -> r *)
Definition typed_withFile : Prop :=
  data_ctx ⊢ₜ withFile
    : type_ty_all (T_Any `Ll)
        ((T_File `Ll -{ `Ll }-> `T 0) -{ `Lf }-> `T 0).

(* let fileExample = withFile<Unit>(fun(f: File'local) Unit()) *)
Definition withFile_example : term :=
  (withFile @ty[ T_Unit ]) @· (λ: T_File `Ll \\ unit_v).

(*   withFile<Unit>(fun(f) Unit())  :  Unit                     *)
Definition typed_withFile_example : Prop := data_ctx ⊢ₜ withFile_example : T_Unit.
(*   withFile<Unit>(fun(f) Unit())  ~~>*  Unit()                *)
Definition red_withFile_example : Prop := withFile_example ==>> unit_v.

(* fun cons[l]<a <: Any'l>(x: a): (List<a>)'l -> List<a> =  *)
(*   fun(xs: List<a>) Cons<a>(x, xs)                        *)
(* The bound is lifetime-polymorphic so the partial application's *)
(* closure (which captures x : a) is tracked at exactly [a]'s     *)
(* lifetime — free instantiations keep a free closure, instead of *)
(* pessimistically forcing local.                                 *)
Definition cons_fn : term :=
  Λl \\
  Λt: T_Any (`L 0) \\
    λ: `T 0 \\
    λ: T_List `Lf (`T 0) \\
      cons_v (`T 0) ($$ 1) ($$ 0).

(*   cons  :  [l]<a <: Any'l>. a -> (List<a> -l-> List<a>)      *)
Definition typed_cons : Prop :=
  data_ctx ⊢ₜ cons_fn
    : type_lt_all (type_ty_all (T_Any (`L 0))
        (`T 0 -{ `Lf }-> T_List `Lf (`T 0) -{ `L 0 }-> T_List `Lf (`T 0))).

(* let list = cons[local]<File'local>(File()) *)
Definition list_example : term :=
  (cons_fn @lt[ `Ll ] @ty[ T_File `Ll ]) @· file_v.

(*   list  :  List<File'local> -local-> List<File'local>        *)
Definition typed_list_example : Prop :=
  data_ctx ⊢ₜ list_example : (T_List `Lf (T_File `Ll) -{ `Ll }-> T_List `Lf (T_File `Ll)).

(*   cons<File'local>(File())  ~~>*  fun(xs) Cons(File(), xs)   *)
Definition red_list_example : Prop :=
  list_example ==>> (λ: T_List `Lf (T_File `Ll) \\
                       cons_v (T_File `Ll) file_v ($$ 0)).

(* fun compose                                           *)
(*   [lf, lg]                                            *)
(*   <a <: Any'local, b <: Any'local, c <: Any'local>    *)
(*   (f: (b)'lf -> c, g: (a)'lg -> b): (a)'lf+lg -> c =  *)
(*   fun(x : a) f(g(x))                                  *)
Definition compose_fn : term :=
  Λl \\
  Λl \\
  Λt: T_Any `Ll \\
  Λt: T_Any `Ll \\
  Λt: T_Any `Ll \\
    λ: (`T 1 -{ `L 1 }-> `T 0) \\
    λ: (`T 2 -{ `L 0 }-> `T 1) \\
    λ: `T 2 \\
      ($$ 2) @· (($$ 1) @· ($$ 0)).

(*   compose : [lf,lg]<a <: Any'local, b <: Any'local, c <: Any'local>. *)
(*     (b -lf-> c) -> (a -lg-> b) -lf-> (a -(lf+lg)-> c)        *)
Definition typed_compose : Prop :=
  data_ctx ⊢ₜ compose_fn
    : type_lt_all (type_lt_all (type_ty_all (T_Any `Ll) (type_ty_all (T_Any `Ll) (type_ty_all (T_Any `Ll)
        ((`T 1 -{ `L 1 }-> `T 0) -{ `Lf }->
         (`T 2 -{ `L 0 }-> `T 1) -{ `L 1 }->
         `T 2 -{ (`L 1 +l `L 0) }-> `T 0))))).

(* let twice = compose[free, free]<Nat, Nat, Nat>(succ, succ)
   The "+2" function; applied to Zero it computes Suc(Suc Zero) = 2. *)
Definition compose_example : term :=
  ((compose_fn @lt[ `Lf ] @lt[ `Lf ]
      @ty[ T_Nat `Lf ] @ty[ T_Nat `Lf ] @ty[ T_Nat `Lf ]) @· succ_fn @· succ_fn) @· zero_v.

(*   compose[free,free]<Nat,Nat,Nat>(succ, succ)(Zero)  :  Nat  *)
Definition typed_compose_example : Prop :=
  data_ctx ⊢ₜ compose_example : T_Nat `Lf.

(*   compose(succ, succ)(Zero)  ~~>*  Suc(Suc(Zero)) = 2        *)
Definition red_compose_example : Prop := compose_example ==>> two_v.

(* let id = fun<a <: Any'local>(x: a) x *)
Definition id_poly : term :=
  Λt: T_Any `Ll \\
    λ: `T 0 \\
      $$ 0.

(*   id  :  <a <: Any'local>. a -> a                            *)
Definition typed_id : Prop :=
  data_ctx ⊢ₜ id_poly : type_ty_all (T_Any `Ll) (`T 0 -{ `Lf }-> `T 0).

(* let idExample = id<Unit>(Unit()) *)
Definition id_example : term := (id_poly @ty[ T_Unit ]) @· unit_v.

(*   id<Unit>(Unit())        :  Unit                            *)
Definition typed_id_example : Prop := data_ctx ⊢ₜ id_example : T_Unit.
(*   id<Unit>(Unit())        ~~>*  Unit()                       *)
Definition red_id_example : Prop := id_example ==>> unit_v.

(* ------------------------------------------------------------------ *)
(* Full F<: with a NON-TRIVIAL type bound.                            *)
(*                                                                    *)
(* Every other bound in this suite is an [Any] type — the escape      *)
(* lattice's own top at some lifetime — so the bound is doing no      *)
(* work beyond the lifetime it carries.  Here the bound is a          *)
(* CONSTRUCTOR type, and the two moves a bound-free (or Kernel-F<:)   *)
(* system cannot make are both exercised:                             *)
(*   - the bound-chase [SA_VarCtx]: a value whose type is a VARIABLE  *)
(*     can be matched on only through the variable's declared bound;  *)
(*   - the CONTRAVARIANT bound of [SA_TyAll]: the two quantifiers'    *)
(*     bounds DIFFER, which the Kernel rule (equal bounds) forbids.   *)
(* ------------------------------------------------------------------ *)

(* fun unwrapOr<a <: Option<Nat>'free>(o: a): Nat =
     match o { case Some(n) -> n; _ -> 0 }
   The scrutinee's type is the variable [a]; T_Match demands a
   constructor type, which only the bound supplies. *)
Definition unwrapOr : term :=
  Λt: T_Option `Lf (T_Nat `Lf) \\
    λ: `T 0 \\
      term_match ($$ 0) some_tag 0 1 ($$ 0) zero_v.

(*   unwrapOr : <a <: Option<Nat>'free>. a -> Nat               *)
Definition typed_unwrapOr : Prop :=
  data_ctx ⊢ₜ unwrapOr
    : type_ty_all (T_Option `Lf (T_Nat `Lf)) (`T 0 -{ `Lf }-> T_Nat `Lf).

(* let unwrapOrExample = unwrapOr<Option<Nat>>(Some(3))
   — instantiated AT its own bound (T_TyApp checks the argument
   against the bound, so the bound is not vacuous here either). *)
Definition unwrapOr_example : term :=
  (unwrapOr @ty[ T_Option `Lf (T_Nat `Lf) ]) @· some_v (T_Nat `Lf) three_v.

(*   unwrapOr<Option<Nat>>(Some(3))  :  Nat                     *)
Definition typed_unwrapOr_example : Prop :=
  data_ctx ⊢ₜ unwrapOr_example : T_Nat `Lf.

(*   unwrapOr<Option<Nat>>(Some(3))  ~~>*  3                    *)
Definition red_unwrapOr_example : Prop := unwrapOr_example ==>> three_v.

(* The contravariant bound of SA_TyAll on its own:
     forall(a <: Any'free).       Unit -> Nat
  <: forall(a <: Option<Nat>'free). Unit -> Nat
   derivable because Option<Nat>'free <: Any'free.  The bounds are
   DISTINCT — this is exactly the full-F<: rule, not the Kernel one. *)
Definition sub_ty_all_bound_contra : Prop :=
  data_ctx ⊢ type_ty_all (T_Any `Lf) (T_Unit -{ `Lf }-> T_Nat `Lf)
        <:: type_ty_all (T_Option `Lf (T_Nat `Lf)) (T_Unit -{ `Lf }-> T_Nat `Lf).

(* let polyConst = fun<a <: Any'free>(u: Unit) 3
   Its term-level consequence: the polymorphic constant DECLARED with
   the wider bound is accepted where the narrower-bound forall is
   demanded (T_Sub over the subtyping above).  (The body is a lambda
   because T_TyLam is prenex — [is_abs body = true].)               *)
Definition poly_const : term := Λt: T_Any `Lf \\ λ: T_Unit \\ three_v.

(*   polyConst : <a <: Option<Nat>'free>. Unit -> Nat           *)
Definition typed_poly_const_at_narrower_bound : Prop :=
  data_ctx ⊢ₜ poly_const
    : type_ty_all (T_Option `Lf (T_Nat `Lf)) (T_Unit -{ `Lf }-> T_Nat `Lf).

(* fun withReader<e <: Any'local, r <: Any'free>(
       f: (Reader<e>'local)'local -> r
   ): (e)'local -> r =
       handle rd: Reader<e> {
           op ask() fun(e: e) resume(e)(e)
       }
       let x: r = f(rd) in
       fun(e: e) x *)
(* [e] may be bound by Any'local: the environment only flows INTO     *)
(* the delimiter (ask's argument is Unit; ask's result enters         *)
(* through the resumption), and the handle's answer type is an        *)
(* arrow, whose escape lifetime is its own annotation — never a       *)
(* chase of [e].  [r] must stay bound by Any'free: the result [x]     *)
(* is captured by the `Lf-annotated closure below, whose capture_lt   *)
(* check keeps a local result from hiding in the returned closure.    *)
Definition withReader : term :=
  Λt: T_Any `Ll \\
  Λt: T_Any `Lf \\
    λ: (T_Reader `Ll (`T 1) -{ `Ll }-> `T 0) \\
      term_handle Reader_tag [`T 1] (`T 1 -{ `Lf }-> `T 0) (`T 1 -{ `Ll }-> `T 0)
        [(0, λ: `T 1 \\
          (($$ 2) @· ($$ 0)) @· ($$ 0))]
        (let: `T 0 <- (($$ 1) @· ($$ 0)) in
         λ: `T 1 \\
           $$ 1).

(*   withReader : <e <: Any'local, r <: Any'free>.              *)
(*     ((Reader<e>'local)'local -> r) -> ((e)'local -> r)       *)
Definition typed_withReader : Prop :=
  full_ctx ⊢ₜ withReader
    : type_ty_all (T_Any `Ll) (type_ty_all (T_Any `Lf)
        ((T_Reader `Ll (`T 1) -{ `Ll }-> `T 0) -{ `Lf }->
         `T 1 -{ `Ll }-> `T 0)).

(* let withReaderExample = withReader<Nat, Nat>(
       fun(rd: Reader<Nat>'local) perform rd.ask()
   )(2)                                              -- = 2 *)
Definition withReader_example : term :=
  (withReader @ty[ T_Nat `Lf ] @ty[ T_Nat `Lf ])
    @· (λ: T_Reader `Ll (T_Nat `Lf) \\ term_perform ($$ 0) 0 [] (T_Nat `Lf) unit_v)
    @· two_v.

(*   withReader_example : Nat                                   *)
Definition typed_withReader_example : Prop :=
  full_ctx ⊢ₜ withReader_example : T_Nat `Lf.

(*   withReader<Nat,Nat>(fun(rd) perform rd.ask())(2)  ~~>*  2  *)
Definition red_withReader_example : Prop := withReader_example ==>> two_v.

(* fun withConsumer<e <: Any'local, r <: Any'free>(
       env: e,
       k: (e)'free -> r
   ): r =
       handle rd: Reader<e> { op ask() resume(env) }
       let a: e = perform rd.ask() in
       k(a) *)
(* The CONSUMER-PASSING (CPS exit) pattern of the Any'local           *)
(* playbook: an [e]-value cannot cross the boundary itself (its       *)
(* lifetime chases to the Any'local bound), so the caller passes a    *)
(* consumer k : e -free-> r IN, the body applies it INSIDE the        *)
(* delimiter, and only the escapable result [r] crosses.  Unlike      *)
(* [withReader], the handle's answer type is the bare variable [r] —  *)
(* escapable by its own Any'free bound, no arrow annotation needed.   *)
(* The k-taking arrow is annotated `Ll because that closure captures  *)
(* [env], whose type's lifetime chases to local.                      *)
Definition withConsumer : term :=
  Λt: T_Any `Ll \\
  Λt: T_Any `Lf \\
    λ: `T 1 \\
    λ: (`T 1 -{ `Lf }-> `T 0) \\
      term_handle Reader_tag [`T 1] (`T 0) (`T 0)
        [(0, ($$ 1) @· ($$ 3))]
        (let: `T 1 <- term_perform ($$ 0) 0 [] (`T 1) unit_v in
         ($$ 2) @· ($$ 0)).

(*   withConsumer : <e <: Any'local, r <: Any'free>.            *)
(*     e -> ((e)'free -> r)'local -> r                          *)
Definition typed_withConsumer : Prop :=
  full_ctx ⊢ₜ withConsumer
    : type_ty_all (T_Any `Ll) (type_ty_all (T_Any `Lf)
        (`T 1 -{ `Lf }-> ((`T 1 -{ `Lf }-> `T 0) -{ `Ll }-> `T 0))).

(* let withConsumer_example =
     withConsumer<Nat'local, Nat'free>(
       2,
       fun(x: Nat'local) match x { Suc(_) -> 3 ; _ -> Zero })   -- = 3
   The environment enters at the CONFINED instantiation Nat'local
   (the free numeral 2 is subsumed into it); the consumer inspects
   the local value inside the delimiter and exports only the free
   numeral it derives from the inspection.                            *)
Definition withConsumer_example : term :=
  (withConsumer @ty[ T_Nat `Ll ] @ty[ T_Nat `Lf ])
    @· two_v
    @· (λ: T_Nat `Ll \\ term_match ($$ 0) suc_tag 0 1 three_v zero_v).

(*   withConsumer_example : Nat                                 *)
Definition typed_withConsumer_example : Prop :=
  full_ctx ⊢ₜ withConsumer_example : T_Nat `Lf.

(*   withConsumer<Nat'local,Nat'free>(2, fun(x) match x {...})  *)
(*     ~~>*  3                                                  *)
Definition red_withConsumer_example : Prop := withConsumer_example ==>> three_v.

(* let reader_example =                            *)
(*   handle r: Reader<Nat> { op ask() resume(2) }  *)
(*   perform r.ask()                               *)
Definition reader_example_op_body : term := ($$ 1) @· two_v.
Definition reader_example : term :=
  term_handle Reader_tag [T_Nat `Lf] (T_Nat `Lf) (T_Nat `Lf) [(0, reader_example_op_body)]
    (term_perform ($$ 0) 0 [] (T_Nat `Lf) unit_v).

(*   reader_example  :  Nat                                     *)
Definition typed_reader_example : Prop :=
  full_ctx ⊢ₜ reader_example : T_Nat `Lf.

(*   handle { ask() resume(2) } perform ask()  ~~>*  2          *)
Definition red_reader_example : Prop := reader_example ==>> two_v.

(* let reader_sum_example =
     handle r: Reader<Nat> { op ask() resume(2) }
     let a = perform r.ask() in
     let b = perform r.ask() in
     let c = perform r.ask() in
     sum3(a, sum3(b, c))
   Three asks under one delimiter; the handler answers 2 every time,
   and the bounded sum validates all three results: 2+(2+2) = 6.      *)
Definition reader_sum_example : term :=
  term_handle Reader_tag [T_Nat `Lf] (T_Nat `Lf) (T_Nat `Lf)
    [(0, reader_example_op_body)]
    (let: T_Nat `Lf <- term_perform ($$ 0) 0 [] (T_Nat `Lf) unit_v in
     let: T_Nat `Lf <- term_perform ($$ 1) 0 [] (T_Nat `Lf) unit_v in
     let: T_Nat `Lf <- term_perform ($$ 2) 0 [] (T_Nat `Lf) unit_v in
     (sum3_fn @· ($$ 2)) @· ((sum3_fn @· ($$ 1)) @· ($$ 0))).

(*   reader_sum_example  :  Nat                                 *)
Definition typed_reader_sum_example : Prop :=
  full_ctx ⊢ₜ reader_sum_example : T_Nat `Lf.

(*   handle { ask() resume(2) } sum of three asks  ~~>*  6      *)
Definition red_reader_sum_example : Prop := reader_sum_example ==>> six_v.

(* ================================================================== *)
(*   effect State<s> { op get(): s ; op put(s): Unit }                *)
(* get = operation index 0, put = operation index 1.                  *)
(* ================================================================== *)

Definition State_tag : eff_tag := 105.
Definition T_State (l : lifetime) (S : type) : type := type_ctor State_tag l [S].

Definition state_sig : binding :=
  bind_eff State_tag 1 [(0, T_Unit, `T 0); (0, `T 0, T_Unit)].

(* [state_ctx]: [full_ctx] extended with the State declaration.       *)
Definition state_ctx : ctx := state_sig :: full_ctx.

(* handle st: State<Nat> {
     op get(u)  = fun(s: Nat) resume(s)(s)      -- clause for index 0
     op put(s') = fun(_: Nat) resume(Unit())(s') -- clause for index 1
   }
   (let a = perform st.get() in     -- fires index 0
    let _ = perform st.put(3) in    -- fires index 1
    let b = perform st.get() in     -- fires index 0 again
    fun(s: Nat) b)
   — state-passing, applied to the initial state 2; evaluates to 3.   *)
Definition state_get_body : term :=
  λ: T_Nat `Lf \\ (($$ 2) @· ($$ 0)) @· ($$ 0).
Definition state_put_body : term :=
  λ: T_Nat `Lf \\ (($$ 2) @· unit_v) @· ($$ 1).

Definition state_example_handler : term :=
  term_handle State_tag [T_Nat `Lf]
    (T_Nat `Lf -{ `Lf }-> T_Nat `Lf)
    (T_Nat `Lf -{ `Ll }-> T_Nat `Lf)
    [(0, state_get_body); (0, state_put_body)]
    (let: T_Nat `Lf <- term_perform ($$ 0) 0 [] (T_Nat `Lf) unit_v in
     let: T_Unit <- term_perform ($$ 1) 1 [] T_Unit three_v in
     let: T_Nat `Lf <- term_perform ($$ 2) 0 [] (T_Nat `Lf) unit_v in
     λ: T_Nat `Lf \\ $$ 1).

Definition state_example : term := state_example_handler @· two_v.

(*   state_example : Nat — the two-operation handler            *)
Definition typed_state_example : Prop :=
  state_ctx ⊢ₜ state_example : T_Nat `Lf.

(*   state_example  ~~>*  3 : both operations of the two-op     *)
(*   declaration fire — get (index 0) twice and put (index 1)   *)
(*   once, selected by nth_error in H_Perform.                  *)
Definition red_state_example : Prop := state_example ==>> three_v.

(* handle st: State<Nat> { get/put as in state_example }
   (let a = perform st.get() in     -- reads the initial state: 2
    let _ = perform st.put(3) in
    let b = perform st.get() in     -- reads the updated state: 3
    fun(s: Nat) sum3(a, b))
   — applied to the initial state 2; the sum validates the reads
   AROUND the put: 2+3 = 5.                                           *)
Definition state_sum_example_handler : term :=
  term_handle State_tag [T_Nat `Lf]
    (T_Nat `Lf -{ `Lf }-> T_Nat `Lf)
    (T_Nat `Lf -{ `Ll }-> T_Nat `Lf)
    [(0, state_get_body); (0, state_put_body)]
    (let: T_Nat `Lf <- term_perform ($$ 0) 0 [] (T_Nat `Lf) unit_v in
     let: T_Unit <- term_perform ($$ 1) 1 [] T_Unit three_v in
     let: T_Nat `Lf <- term_perform ($$ 2) 0 [] (T_Nat `Lf) unit_v in
     λ: T_Nat `Lf \\ (sum3_fn @· ($$ 3)) @· ($$ 1)).

Definition state_sum_example : term := state_sum_example_handler @· two_v.

(*   state_sum_example : Nat                                    *)
Definition typed_state_sum_example : Prop :=
  state_ctx ⊢ₜ state_sum_example : T_Nat `Lf.

(*   state_sum_example  ~~>*  5 : sum of the get before and the *)
(*   get after the put.                                         *)
Definition red_state_sum_example : Prop := state_sum_example ==>> five_v.

(* error (the Listing-1 leak):
     handle st: State<Nat> { op get(u) resume(0); op put(s) resume(Unit()) }
     in st
   — the handler body returns the capability ITSELF, so the handle's
   declared body type T_B is the capability type
     T_State `Ll (Nat'free)      (local by construction).
   T_Handle demands `lt_of_ty_G Γ T_B <: lt_free`, which fails on the
   local capability type, so the term has NO typing derivation at ANY
   type — [leak_state_rejected] (ExamplesRejection.v).  The clauses
   are innocuous single-resume answers (get answers 0, put
   acknowledges), each typable at its T_Handle premise instance: only
   the escape is at fault.                                            *)
Definition leak_state : term :=
  term_handle State_tag [T_Nat `Lf]
    (T_State `Ll (T_Nat `Lf)) (T_State `Ll (T_Nat `Lf))
    [(0, ($$ 1) @· zero_v); (0, ($$ 1) @· unit_v)]
    ($$ 0).

(* ================================================================== *)
(*   effect Chan<s> { op send(s): Unit ; op poll<a>(): Option<a> }    *)
(*                                                                    *)
(* The multi-operation × β-polymorphic combination.  send (index 0)   *)
(* has no β-parameter and takes the effect's own parameter s; poll    *)
(* (index 1) is β-polymorphic and is INSTANTIATED at the perform site *)
(* — twice in one run, at two different types.                        *)
(*                                                                    *)
(* poll's β occurs ONLY in its result.  That is what makes it the     *)
(* isolating test for T_Perform's Forall-premise on the β-arguments:  *)
(* poll's instantiated signature is Unit at EVERY instantiation, so a *)
(* local β-argument fails that premise and no other                   *)
(* ([poll_local_beta_rejected], ExamplesRejection.v).                 *)
(*                                                                    *)
(* Schema indices follow [inst_op_all_args]: α-vars innermost         *)
(* (`T 0 = s), β-vars outermost (`T 1 = a).                           *)
(* ================================================================== *)

Definition Chan_tag : eff_tag := 106.
Definition T_Chan (l : lifetime) (S : type) : type := type_ctor Chan_tag l [S].

Definition chan_sig : binding :=
  bind_eff Chan_tag 1 [(0, `T 0, T_Unit); (1, T_Unit, T_Option `Lf (`T 1))].

(* [chan_ctx]: [full_ctx] extended with the Chan declaration.         *)
Definition chan_ctx : ctx := chan_sig :: full_ctx.

(* handle c: Chan<Nat> {
     op send(x)    resume(Unit())        -- clause for index 0
     op poll<a>(u) resume(None<a>())     -- clause for index 1
   }
   (let _ = perform c.send(3)      in    -- fires index 0
    let o = perform c.poll<Nat>()  in    -- fires index 1 at Nat
    let p = perform c.poll<Unit>() in    -- ...and again at Unit
    o)
   The handler answers every poll with None at the β-argument it was
   given, so the run delivers the PAIR of the two answers —
   None<Nat>() and None<Unit>() — each carrying back the type its own
   perform was instantiated at.  The two instantiations are therefore
   visible in the normal form, not merely performed: the [poll] clause
   is typed ONCE against the schema, and the two performs differ only
   in Ss.                                                             *)
Definition chan_send_body : term := ($$ 1) @· unit_v.
Definition chan_poll_body : term := ($$ 1) @· none_v (`T 0).

(* The answer type: the two β-instantiations side by side.           *)
Definition T_ChanAnswer : type :=
  T_Pair `Lf (T_Option `Lf (T_Nat `Lf)) (T_Option `Lf T_Unit).

Definition chan_example : term :=
  term_handle Chan_tag [T_Nat `Lf] T_ChanAnswer T_ChanAnswer
    [(0, chan_send_body); (1, chan_poll_body)]
    (let: T_Unit <- term_perform ($$ 0) 0 [] T_Unit three_v in
     let: T_Option `Lf (T_Nat `Lf) <-
       term_perform ($$ 1) 1 [T_Nat `Lf] (T_Option `Lf (T_Nat `Lf)) unit_v in
     let: T_Option `Lf T_Unit <-
       term_perform ($$ 2) 1 [T_Unit] (T_Option `Lf T_Unit) unit_v in
     pair_v (T_Option `Lf (T_Nat `Lf)) (T_Option `Lf T_Unit) ($$ 1) ($$ 0)).

(*   chan_example : Pair<Option<Nat>, Option<Unit>>  — two      *)
(*   operations, one β-polymorphic, instantiated at two types   *)
Definition typed_chan_example : Prop :=
  chan_ctx ⊢ₜ chan_example : T_ChanAnswer.

(*   chan_example  ~~>*  Pair(None<Nat>(), None<Unit>())        *)
Definition red_chan_example : Prop :=
  chan_example ==>> pair_v (T_Option `Lf (T_Nat `Lf)) (T_Option `Lf T_Unit)
                     (none_v (T_Nat `Lf)) (none_v T_Unit).

(* fun withException<e <: Any'free, r <: Any'free>(
       f: (Exception<e>'local)'local -> r
   ): Result<e, r> =
       handle h: Exception<e> {
           op throw<a>(e) Error<e, r>(e)
       }
       Ok<e, r>(f(h))
   [f]'s own arrow is LOCAL (contravariant position, most permissive
   demand) — as in [withReader].                                      *)
Definition withException_op_body : term :=
  error_v (`T 2) (`T 1) ($$ 0).

Definition withException : term :=
  Λt: T_Any `Lf \\
  Λt: T_Any `Lf \\
    λ: (T_Exception `Ll (`T 1) -{ `Ll }-> `T 0) \\
      term_handle Exception_tag [`T 1]
        (T_Result `Lf (`T 1) (`T 0)) (T_Result `Lf (`T 1) (`T 0)) [(1, withException_op_body)]
        (ok_v (`T 1) (`T 0) (($$ 1) @· ($$ 0))).

(*   withException : <e <: Any'free, r <: Any'free>.            *)
(*     ((Exception<e>'local) -local-> r) -> Result<e, r>        *)
Definition typed_withException : Prop :=
  full_ctx ⊢ₜ withException
    : type_ty_all (T_Any `Lf) (type_ty_all (T_Any `Lf)
        ((T_Exception `Ll (`T 1) -{ `Ll }-> `T 0) -{ `Lf }->
         T_Result `Lf (`T 1) (`T 0))).

(* let exception_example =                                             *)
(*   withException<Nat, File>(fun(h: Exception<Nat>'local)             *)
(*                              perform h.throw<File>(3))              *)
Definition exception_example_body : term :=
  term_perform ($$ 0) 0 [T_File `Lf] (T_File `Lf) three_v.

Definition exception_example : term :=
  (withException @ty[ T_Nat `Lf ] @ty[ T_File `Lf ]) @·
    (λ: T_Exception `Ll (T_Nat `Lf) \\
      exception_example_body).

(*   exception_example  :  Result<Nat, File>                    *)
Definition typed_exception_example : Prop :=
  full_ctx ⊢ₜ exception_example : T_Result `Lf (T_Nat `Lf) (T_File `Lf).

(*   withException<Nat,File>(fun(h) throw 3)  ~~>*  Error(3)    *)
(* The abortive handler: the captured continuation (the Ok      *)
(* frame) is discarded — the op clause never resumes.           *)
Definition red_exception_example : Prop :=
  exception_example ==>> error_v (T_Nat `Lf) (T_File `Lf) three_v.

(* fun lazyMap[lf, la, lb]<a <: Any'la, b <: Any'lb>(
       xs: LazyList<a>'la, f: (a)'lf -> b
   ): LazyList<b>'lf+la =
       match xs {
           case LNil() -> LNil<b>()
           case LCons(h, t) -> LCons[lf+la, lf+la, lf+la, lf+la]<b>(
               fun() f(h()),
               fun() lazyMap[lf, la, lb]<a, b>(t(), f))
           _ -> LNil<b>()
       }
   The core calculus has no fixpoint; this is the open recursive body
   under a self binder at de Bruijn index 2. *)
Definition lazyMap_body : term :=
  term_match ($$ 1) lnil_tag 0 0
    (term_ctor lnil_tag `Lf [] [`T 0] [])
    (term_match ($$ 1) lcons_tag 4 2
       (term_ctor lcons_tag (`L 6 +l `L 5)
          [`L 6 +l `L 5; `L 6 +l `L 5; `L 6 +l `L 5; `L 6 +l `L 5]
          [`T 0]
          [ λ: T_Unit \\
              ($$ 3) @· (($$ 1) @· unit_v)
          ; λ: T_Unit \\
              (($$ 5) @· (($$ 2) @· unit_v)) @· ($$ 3) ])
       (term_ctor lnil_tag `Lf [] [`T 0] [])).

(* The explicit binder context of [lazyMap_body] (innermost first):   *)
(*   f    : (a)'lf -> b                                               *)
(*   xs   : LazyList<a>'la                                            *)
(*   self : LazyList<a>'la -(lf+la)-> ((a)'lf -> b) -(lf+la)->        *)
(*            LazyList<b>'(lf+la)                                     *)
(*   b <: Any'lb, a <: Any'la,  [lb, la, lf]                          *)
(* over data_ctx.                                                     *)
(* (lf = `L 2, la = `L 1, lb = `L 0; a = `T 1, b = `T 0.)             *)
Definition lazyMap_ctx : ctx :=
  bind_tm (`T 1 -{ `L 2 }-> `T 0)
  :: bind_tm (T_LazyList (`L 1) (`T 1))
  :: bind_tm (T_LazyList (`L 1) (`T 1) -{ `L 2 +l `L 1 }->
       ((`T 1 -{ `L 2 }-> `T 0) -{ `L 2 +l `L 1 }->
        T_LazyList (`L 2 +l `L 1) (`T 0)))
  :: bind_ty (T_Any (`L 0))
  :: bind_ty (T_Any (`L 1))
  :: bind_lt `Ll
  :: bind_lt `Ll
  :: bind_lt `Ll
  :: data_ctx.

(*   lazyMap_body : LazyList<b>'(lf+la)                         *)
(*     (open, under lazyMap_ctx)                                *)
Definition typed_lazyMap_body : Prop :=
  lazyMap_ctx ⊢ₜ lazyMap_body : T_LazyList (`L 2 +l `L 1) (`T 0).

(* fun mapFirst[la, lb, lc]<a <: Any'la, b <: Any'lb, c <: Any'lc>(
       dflt: Pair<c, b>, p: Pair<a, b>, f: (a)'local -> c
   ): Pair<c, b> =
       match p { case Pair(x, y) -> Pair<c, b>(f(x), y); _ -> dflt }
   A match must carry a well-typed no-branch even when the scrutinee's
   datatype has a single constructor (the calculus has no exhaustiveness
   analysis), and Pair<c, b> is not constructible from p and f alone —
   hence the explicit default.  *)
Definition mapFirst : term :=
  Λl \\
  Λl \\
  Λl \\
  Λt: T_Any (`L 2) \\
  Λt: T_Any (`L 1) \\
  Λt: T_Any (`L 0) \\
    λ: T_Pair `Lf (`T 0) (`T 1) \\
    λ: T_Pair `Lf (`T 2) (`T 1) \\
    λ: (`T 2 -{ `Ll }-> `T 0) \\
      term_match ($$ 1) pair_tag 0 2
        (term_ctor pair_tag `Lf [] [`T 0; `T 1]
           [($$ 2) @· ($$ 0); $$ 1])
        ($$ 2).

(*   mapFirst : [la,lb,lc]<a <: Any'la, b <: Any'lb, c <: Any'lc>. *)
(*     Pair<c,b> -> Pair<a,b> -local->                             *)
(*       ((a)'local -> c) -local-> Pair<c,b>                       *)
Definition typed_mapFirst : Prop :=
  data_ctx ⊢ₜ mapFirst
    : type_lt_all (type_lt_all (type_lt_all
        (type_ty_all (T_Any (`L 2)) (type_ty_all (T_Any (`L 1)) (type_ty_all (T_Any (`L 0))
          (T_Pair `Lf (`T 0) (`T 1) -{ `Lf }->
           T_Pair `Lf (`T 2) (`T 1) -{ `Ll }->
           (`T 2 -{ `Ll }-> `T 0) -{ `Ll }->
           T_Pair `Lf (`T 0) (`T 1))))))).

(* fun foldEndo[l0](n: Nat'l0, endo: EndoI'l0): Nat'l0 =
     match endo { case EndoI(f) -> f(3); _ -> n }
   (n doubles as the match's well-typed default branch.) *)
Definition foldEndo : term :=
  Λl \\
    λ: T_Nat (`L 0) \\
    λ: T_EndoI (`L 0) \\
      term_match ($$ 0) endoi_tag 1 1 (($$ 0) @· three_v) ($$ 1).

(*   foldEndo : [l]. Nat'l -> EndoI'l -l-> Nat'l                *)
Definition typed_foldEndo : Prop :=
  data_ctx ⊢ₜ foldEndo
    : type_lt_all (T_Nat (`L 0) -{ `Lf }-> (T_EndoI (`L 0) -{ `L 0 }-> T_Nat (`L 0))).

(* let mapFirstExample = mapFirst[free,free,free]<Nat,Nat,Nat>(
       Pair(0, 0), Pair(2, 3), succ)          -- = Pair(3, 3) *)
Definition mapFirst_example : term :=
  ((mapFirst @lt[ `Lf ] @lt[ `Lf ] @lt[ `Lf ]
      @ty[ T_Nat `Lf ] @ty[ T_Nat `Lf ] @ty[ T_Nat `Lf ])
    @· pair_v (T_Nat `Lf) (T_Nat `Lf) zero_v zero_v
    @· pair_v (T_Nat `Lf) (T_Nat `Lf) two_v three_v)
    @· succ_fn.

(*   mapFirst_example : Pair<Nat, Nat>                          *)
Definition typed_mapFirst_example : Prop :=
  data_ctx ⊢ₜ mapFirst_example : T_Pair `Lf (T_Nat `Lf) (T_Nat `Lf).

(*   mapFirst(Pair(0,0), Pair(2,3), succ)  ~~>*  Pair(3, 3)     *)
Definition red_mapFirst_example : Prop :=
  mapFirst_example ==>> pair_v (T_Nat `Lf) (T_Nat `Lf) three_v three_v.

(* EndoI[free](succ) *)
Definition endoi_v : term := term_ctor endoi_tag `Lf [`Lf] [] [succ_fn].

(* let foldEndoExample = foldEndo[free](2, EndoI(succ))   -- = succ(3) = 4 *)
Definition foldEndo_example : term :=
  (foldEndo @lt[ `Lf ]) @· two_v @· endoi_v.

(*   foldEndo_example : Nat                                     *)
Definition typed_foldEndo_example : Prop :=
  data_ctx ⊢ₜ foldEndo_example : T_Nat `Lf.

(*   foldEndo[free](2, EndoI(succ))  ~~>*  4                    *)
Definition red_foldEndo_example : Prop := foldEndo_example ==>> four_v.

(* fun withId<r <: Any'free>(f: (Id'local)'local -> r): r =
     handle h: Id { op id<a>(x) resume(x) } f(h)
   [f]'s own arrow is LOCAL (contravariant position, most permissive
   demand) — as in [withReader].                                     *)
Definition withId_op_body : term := ($$ 1) @· ($$ 0).
Definition withId : term :=
  Λt: T_Any `Lf \\
    λ: (T_Id `Ll -{ `Ll }-> `T 0) \\
      term_handle Id_tag [] (`T 0) (`T 0) [(1, withId_op_body)] (($$ 1) @· ($$ 0)).

(*   withId  :  <r <: Any'free>. ((Id'local) -local-> r) -> r   *)
Definition typed_withId : Prop :=
  full_ctx ⊢ₜ withId
    : type_ty_all (T_Any `Lf)
        ((T_Id `Ll -{ `Ll }-> `T 0) -{ `Lf }-> `T 0).

(* let optionality_example =
     handle o: Optionality { op mkSome<b>(x) resume(Some<b>(x)) }
     perform o.mkSome<Nat>(3) *)
Definition optionality_op_body : term :=
  ($$ 1) @· (some_v (`T 0) ($$ 0)).

Definition optionality_example : term :=
  term_handle Optionality_tag []
    (T_Option `Lf (T_Nat `Lf)) (T_Option `Lf (T_Nat `Lf)) [(1, optionality_op_body)]
    (term_perform ($$ 0) 0 [T_Nat `Lf] (T_Option `Lf (T_Nat `Lf)) three_v).

(*   optionality_example  :  Option<Nat>                        *)
Definition typed_optionality_example : Prop :=
  full_ctx ⊢ₜ optionality_example : T_Option `Lf (T_Nat `Lf).

(*   handle { mkSome(x) resume(Some(x)) } perform mkSome(3)     *)
(*       ~~>*  Some(3)                                          *)
Definition red_optionality_example : Prop :=
  optionality_example ==>> some_v (T_Nat `Lf) three_v.

(* let withIdExample = withId<Nat>(fun(h: Id'local)
       perform h.id<Nat>(2))                         -- = 2 *)
Definition withId_example : term :=
  (withId @ty[ T_Nat `Lf ])
    @· (λ: T_Id `Ll \\ term_perform ($$ 0) 0 [T_Nat `Lf] (T_Nat `Lf) two_v).

(*   withId_example : Nat                                       *)
Definition typed_withId_example : Prop :=
  full_ctx ⊢ₜ withId_example : T_Nat `Lf.

(*   withId<Nat>(fun(h) perform h.id<Nat>(2))  ~~>*  2          *)
Definition red_withId_example : Prop := withId_example ==>> two_v.

(* let multishot_example =
     handle r: Reader<Nat> {
       op ask() let x = resume(2) in let y = resume(3) in sum3(x, y)
     }
     perform r.ask()
   The op clause resumes TWICE: the captured continuation is re-run,
   re-installing the delimiter each time (multi-shot), and the sum
   validates both resumption results: 2+3 = 5.               -- = 5 *)
Definition multishot_op_body : term :=
  let: T_Nat `Lf <- ($$ 1) @· two_v in
  let: T_Nat `Lf <- ($$ 2) @· three_v in
  (sum3_fn @· ($$ 1)) @· ($$ 0).

Definition multishot_example : term :=
  term_handle Reader_tag [T_Nat `Lf] (T_Nat `Lf) (T_Nat `Lf) [(0, multishot_op_body)]
    (term_perform ($$ 0) 0 [] (T_Nat `Lf) unit_v).

(*   multishot_example : Nat                                    *)
Definition typed_multishot_example : Prop :=
  full_ctx ⊢ₜ multishot_example : T_Nat `Lf.

(*   handle { ask() sum3(resume(2), resume(3)) } perform ask()  *)
(*       ~~>*  5                                                *)
Definition red_multishot_example : Prop := multishot_example ==>> five_v.

(* let forward_example =
     handle h: Exception<Nat> { op throw<a>(e) Error<Nat,File>(e) }
     Ok<Nat,File>(
       handle r: Reader<Nat> { op ask() resume(2) }
       let x: Nat = perform r.ask() in
       perform h.throw<File>(x))
   The throw is performed UNDER the live Reader delimiter: the perform
   crosses it (an unrelated handler is transparent, pem_handler_m) and
   the abortive clause discards both the Ok frame and the inner
   delimiter.                                    -- = Error(2) *)
Definition forward_inner_body : term :=
  let: T_Nat `Lf <- term_perform ($$ 0) 0 [] (T_Nat `Lf) unit_v in
  term_perform ($$ 2) 0 [T_File `Lf] (T_File `Lf) ($$ 0).

Definition forward_example : term :=
  term_handle Exception_tag [T_Nat `Lf]
    (T_Result `Lf (T_Nat `Lf) (T_File `Lf)) (T_Result `Lf (T_Nat `Lf) (T_File `Lf))
    [(1, error_v (T_Nat `Lf) (T_File `Lf) ($$ 0))]
    (ok_v (T_Nat `Lf) (T_File `Lf)
      (term_handle Reader_tag [T_Nat `Lf] (T_File `Lf) (T_File `Lf)
        [(0, ($$ 1) @· two_v)]
        forward_inner_body)).

(*   forward_example : Result<Nat, File>                        *)
Definition typed_forward_example : Prop :=
  full_ctx ⊢ₜ forward_example : T_Result `Lf (T_Nat `Lf) (T_File `Lf).

(*   forward_example  ~~>*  Error(2)                            *)
Definition red_forward_example : Prop :=
  forward_example ==>> error_v (T_Nat `Lf) (T_File `Lf) two_v.

(* let delegate_example =
     handle r1: Reader<Nat> { op ask() resume(2) }
     handle r2: Reader<Nat> {
       op ask() let a = perform r1.ask() in resume(sum3(a, 3))
     }
     perform r2.ask()
   An operation clause that itself performs an operation of the OUTER
   handler: the inner Reader's ask DELEGATES to the outer one — the
   capability r1 is lexically in scope in the clause ($$2 above the
   clause's arg/resume binders).  When the clause runs it has already
   replaced the inner delimiter (captured into the resumption), so its
   perform reaches the outer handler across a pure context; both
   handlers are the SAME effect (Reader), told apart by their markers —
   handler selection is lexical, through the capability.
                                                     -- = 2+3 = 5 *)
Definition delegate_op_body : term :=
  let: T_Nat `Lf <- term_perform ($$ 2) 0 [] (T_Nat `Lf) unit_v in
  ($$ 2) @· ((sum3_fn @· ($$ 0)) @· three_v).

Definition delegate_example : term :=
  term_handle Reader_tag [T_Nat `Lf] (T_Nat `Lf) (T_Nat `Lf)
    [(0, reader_example_op_body)]
    (term_handle Reader_tag [T_Nat `Lf] (T_Nat `Lf) (T_Nat `Lf)
      [(0, delegate_op_body)]
      (term_perform ($$ 0) 0 [] (T_Nat `Lf) unit_v)).

(*   delegate_example : Nat                                     *)
Definition typed_delegate_example : Prop :=
  full_ctx ⊢ₜ delegate_example : T_Nat `Lf.

(*   handle { ask() resume(2) }                                 *)
(*   handle { ask() resume(sum3(outer ask, 3)) }                *)
(*   perform ask()                              ~~>*  5         *)
Definition red_delegate_example : Prop := delegate_example ==>> five_v.

(* fun getOrElse<t <: Any'local>(default: t, o: Option<t>): t =
     match o { case Some(x) -> x; _ -> default } *)
Definition getOrElse : term :=
  Λt: T_Any `Ll \\
    λ: `T 0 \\
    λ: T_Option `Lf (`T 0) \\
      term_match ($$ 0) some_tag 0 1 ($$ 0) ($$ 1).

(*   getOrElse : <t <: Any'local>. t -> Option<t> -local-> t    *)
Definition typed_getOrElse : Prop :=
  data_ctx ⊢ₜ getOrElse
    : type_ty_all (T_Any `Ll)
        (`T 0 -{ `Lf }-> (T_Option `Lf (`T 0) -{ `Ll }-> `T 0)).

(* getOrElse<Nat>(0, Some(3)) -- = 3   (the yes branch)  *)
Definition getOrElse_some : term :=
  (getOrElse @ty[ T_Nat `Lf ]) @· zero_v @· some_v (T_Nat `Lf) three_v.

(*   getOrElse_some : Nat                                       *)
Definition typed_getOrElse_some : Prop := data_ctx ⊢ₜ getOrElse_some : T_Nat `Lf.
(*   getOrElse<Nat>(0, Some(3))  ~~>*  3   (H_MatchYes)         *)
Definition red_getOrElse_some : Prop := getOrElse_some ==>> three_v.

(* getOrElse<Nat>(0, None())  -- = 0   (the no branch)   *)
Definition getOrElse_none : term :=
  (getOrElse @ty[ T_Nat `Lf ]) @· zero_v @· none_v (T_Nat `Lf).

(*   getOrElse_none : Nat                                       *)
Definition typed_getOrElse_none : Prop := data_ctx ⊢ₜ getOrElse_none : T_Nat `Lf.
(*   getOrElse<Nat>(0, None())   ~~>*  0   (H_MatchNo)          *)
Definition red_getOrElse_none : Prop := getOrElse_none ==>> zero_v.

(* Completing list_example's partial application with Nil. *)
Definition list_example_full : term :=
  list_example @· nil_v (T_File `Ll).

(*   list_example_full : List<File'local>                       *)
Definition typed_list_example_full : Prop :=
  data_ctx ⊢ₜ list_example_full : T_List `Lf (T_File `Ll).
(*   list_example(Nil)  ~~>*  Cons(File(), Nil)                 *)
Definition red_list_example_full : Prop :=
  list_example_full ==>> cons_v (T_File `Ll) file_v (nil_v (T_File `Ll)).

(* ================================================================== *)
(* 4. Negative statements: the commented error examples, stated on    *)
(* the REAL premises of the typing rules.                             *)
(* ================================================================== *)

(* error: testWithState stores a local Reader capability inside free   *)
(* state.  The rejection is stated on the noloc premise of T_Perform / *)
(* T_Handle — `Γ ⊢ₗ lt_of_ty_G Γ S <: lt_free`.  The proof is a        *)
(* certified decision by [nolocb] (Decide.v).                          *)
Definition rejected_testWithState : Prop :=
  ~ (full_ctx ⊢ₗ lt_of_ty_G full_ctx (T_Option `Lf (T_Reader `Ll T_Unit))
        <: lt_free).

(* error: crashEndo tries to existentially forget Trash's local Nat    *)
(* lifetime, which occurs in an INVARIANT position — a constructor     *)
(* type argument — of [trash_field] (Endo's parameter Nat'l).  The     *)
(* witness is a genuine T_Match premise ([elim_ty_n]).                 *)
Definition rejected_crashEndo : Prop :=
  elim_ty_n 1 `Ll var_pos trash_field = None.

(* error: crashBox tries to expose Box's field Option<Nat'local>       *)
(* (= [box_field] at a local lifetime) as escapable.  Stated on the    *)
(* real noloc judgment, decided by [nolocb] (Decide.v).                *)
Definition rejected_crashBox : Prop :=
  ~ (data_ctx ⊢ₗ lt_of_ty_G data_ctx (subst_lt_in_ty 0 `Ll box_field)
        <: lt_free).

(* fun clash(x: Nat'free, y: Nat'local): Unit = Unit()                 *)
(* Positive companion: Unit's lifetime IS escapable — the real noloc   *)
(* judgment is derivable, again by certified decision.                 *)
Definition typed_clash_ignored_local : Prop :=
  data_ctx ⊢ₗ lt_of_ty_G data_ctx T_Unit <: lt_free.
