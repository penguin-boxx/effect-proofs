Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.

(* ================================================================== *)
(* Core examples: definitions and statements only.                     *)
(*                                                                    *)
(* Placement discipline for this file:                                *)
(*   1. term/type/context definitions                                 *)
(*   2. typing statements, as Prop definitions                        *)
(*   3. reduction statements, as Prop definitions                     *)
(*                                                                    *)
(* Proofs of these statements live in ExamplesProofs.v.               *)
(* ================================================================== *)

Module CoreNotation.
  Notation "'`Lf'"     := lt_free.
  Notation "'`Ll'"     := lt_local.
  Notation "'`L' n"    := (lt_var n) (at level 5, format "'`L'  n").
  Notation "l1 '+l' l2" := (lt_min l1 l2) (at level 50, left associativity).

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

Inductive multi_step : term -> term -> Prop :=
  | ms_refl : forall t, multi_step t t
  | ms_step : forall t1 t2 t3,
      t1 ==> t2 -> multi_step t2 t3 -> multi_step t1 t3.

Notation "t '==>>' t'" := (multi_step t t') (at level 40).

(* ================================================================== *)
(* 1. Data declarations                                                *)
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

Definition int_tag   : ctor_tag := 60.
Definition int2_tag  : ctor_tag := 62.
Definition int42_tag : ctor_tag := 642.

Definition lazy_list_tag  : ctor_tag := 70.
Definition lnil_tag       : ctor_tag := 71.
Definition lcons_tag      : ctor_tag := 72.

Definition pair_tag : ctor_tag := 80.

Definition endoi_tag : ctor_tag := 90.
Definition endo_tag  : ctor_tag := 91.
Definition trash_tag : ctor_tag := 92.
Definition box_tag   : ctor_tag := 93.

Definition T_Any (l : lifetime) : type := type_ctor any_tag l [].
Definition T_Unit : type := type_ctor unit_tag `Lf [].
Definition T_Option (l : lifetime) (A : type) : type := type_ctor option_tag l [A].
Definition T_Result (l : lifetime) (E A : type) : type := type_ctor result_tag l [E; A].
Definition T_File (l : lifetime) : type := type_ctor file_tag l [].
Definition T_List (l : lifetime) (A : type) : type := type_ctor list_tag l [A].
Definition T_Int (l : lifetime) : type := type_ctor int_tag l [].
Definition T_LazyList (l : lifetime) (A : type) : type := type_ctor lazy_list_tag l [A].
Definition T_Pair (l : lifetime) (A B : type) : type := type_ctor pair_tag l [A; B].
Definition T_EndoI (l : lifetime) : type := type_ctor endoi_tag l [].
Definition T_Endo (l : lifetime) (A : type) : type := type_ctor endo_tag l [A].
Definition T_Trash (l : lifetime) : type := type_ctor trash_tag l [].
Definition T_Box (l : lifetime) : type := type_ctor box_tag l [].

(* data Unit = Unit *)
Definition unit_sig : binding := bind_ctor unit_tag 0 0 [] T_Unit.

(* data Option<a> = None | Some(a)
   Internally the datatype carries an explicit result lifetime la. *)
Definition none_sig : binding :=
  bind_ctor none_tag 1 1 [] (T_Option (`L 0) (`T 0)).
Definition some_sig : binding :=
  bind_ctor some_tag 1 1 [`T 0] (T_Option (`L 0) (`T 0)).

(* data Result<e, a> = Error(e) | Ok(a) *)
Definition error_sig : binding :=
  bind_ctor error_tag 1 2 [`T 0] (T_Result (`L 0) (`T 0) (`T 1)).
Definition ok_sig : binding :=
  bind_ctor ok_tag 1 2 [`T 1] (T_Result (`L 0) (`T 0) (`T 1)).

(* data File = File *)
Definition file_sig : binding := bind_ctor file_tag 0 0 [] (T_File `Lf).

(* data List<a> = Nil | Cons(a, List<a>) *)
Definition nil_sig : binding :=
  bind_ctor nil_tag 1 1 [] (T_List (`L 0) (`T 0)).
Definition cons_sig : binding :=
  bind_ctor cons_tag 1 1 [`T 0; T_List (`L 0) (`T 0)] (T_List (`L 0) (`T 0)).

(* Int is represented as a tiny constructor family for the literals used here. *)
Definition int2_sig : binding := bind_ctor int2_tag 0 0 [] (T_Int `Lf).
Definition int42_sig : binding := bind_ctor int42_tag 0 0 [] (T_Int `Lf).

(* data LazyList<a> = LNil | LCons[lh, lt, ll](()'lh -> a, ()'lt -> LazyList<a>'ll) *)
Definition lnil_sig : binding :=
  bind_ctor lnil_tag 1 1 [] (T_LazyList (`L 0) (`T 0)).
Definition lcons_sig : binding :=
  bind_ctor lcons_tag 4 1
    [ T_Unit -{ `L 2 }-> `T 0
    ; T_Unit -{ `L 1 }-> T_LazyList (`L 0) (`T 0) ]
    (T_LazyList (`L 3) (`T 0)).

(* data Pair<a, b> = Pair(a, b) *)
Definition pair_sig : binding :=
  bind_ctor pair_tag 1 2 [`T 0; `T 1] (T_Pair (`L 0) (`T 0) (`T 1)).

(* data EndoI = EndoI[l]((Int'l) -> Int'l) *)
Definition endoi_sig : binding :=
  bind_ctor endoi_tag 1 0 [T_Int (`L 0) -{ `Lf }-> T_Int (`L 0)] (T_EndoI (`L 0)).

(* data Endo<a> = Endo((a) -> a) *)
Definition endo_sig : binding :=
  bind_ctor endo_tag 1 1 [`T 0 -{ `Lf }-> `T 0] (T_Endo (`L 0) (`T 0)).

(* data Trash = Trash[l](Endo<Int'l>) *)
Definition trash_sig : binding :=
  bind_ctor trash_tag 1 0 [T_Endo (`L 0) (T_Int (`L 0))] (T_Trash (`L 0)).

(* data Box = Box[l](Option<Int'l>) *)
Definition box_sig : binding :=
  bind_ctor box_tag 1 0 [T_Option (`L 0) (T_Int (`L 0))] (T_Box (`L 0)).

Definition data_ctx : ctx :=
  [ box_sig; trash_sig; endo_sig; endoi_sig; pair_sig; lcons_sig; lnil_sig
  ; int42_sig; int2_sig; cons_sig; nil_sig; file_sig; ok_sig; error_sig
  ; some_sig; none_sig; unit_sig ].

(* ================================================================== *)
(* 2. Effects                                                         *)
(* ================================================================== *)

Definition Reader_tag      : eff_tag := 100.
Definition State_tag       : eff_tag := 101.
Definition Exception_tag   : eff_tag := 102.
Definition Id_tag          : eff_tag := 103.
Definition Optionality_tag : eff_tag := 104.

Definition cmd_tag : ctor_tag := 110.
Definition get_tag : ctor_tag := 111.
Definition put_tag : ctor_tag := 112.

Definition T_Reader (l : lifetime) (E : type) : type := type_ctor Reader_tag l [E].
Definition T_State (l : lifetime) (S : type) : type := type_ctor State_tag l [S].
Definition T_Exception (l : lifetime) (E : type) : type := type_ctor Exception_tag l [E].
Definition T_Id (l : lifetime) : type := type_ctor Id_tag l [].
Definition T_Optionality (l : lifetime) : type := type_ctor Optionality_tag l [].
Definition T_Cmd (l : lifetime) (S : type) : type := type_ctor cmd_tag l [S].

(* effect Reader<e> { op ask(): e } *)
Definition reader_sig : binding := bind_eff Reader_tag 1 0 T_Unit (`T 0).

(* effect State<s> { op get(): s; op put(s): Unit }
   The core calculus has one operation per effect, so State is encoded
   as a command effect Cmd<s> -> s. Put returns the new state. *)
Definition get_sig : binding := bind_ctor get_tag 0 1 [] (T_Cmd `Lf (`T 0)).
Definition put_sig : binding := bind_ctor put_tag 0 1 [`T 0] (T_Cmd `Lf (`T 0)).
Definition state_sig : binding := bind_eff State_tag 1 0 (T_Cmd `Lf (`T 0)) (`T 0).

(* effect Exception<e> { op throw<a>(e): a } *)
Definition exception_sig : binding := bind_eff Exception_tag 1 1 (`T 0) (`T 1).

(* effect Id { op id<a>(a): a } *)
Definition id_sig : binding := bind_eff Id_tag 0 1 (`T 0) (`T 0).

(* effect Optionality { op mkSome<a>(a): Option<a> } *)
Definition optionality_sig : binding :=
  bind_eff Optionality_tag 0 1 (`T 0) (T_Option `Lf (`T 0)).

Definition effect_ctx : ctx :=
  [ optionality_sig; id_sig; exception_sig; state_sig; put_sig; get_sig; reader_sig ].

Definition full_ctx : ctx := data_ctx ++ effect_ctx.

(* ================================================================== *)
(* 3. Term definitions                                                *)
(* ================================================================== *)

(* Unit() *)
Definition unit_v : term := term_ctor unit_tag `Lf [] [] [].

(* File() *)
Definition file_v : term := term_ctor file_tag `Lf [] [] [].

(* 2 and 42 *)
Definition int2_v : term := term_ctor int2_tag `Lf [] [] [].
Definition int42_v : term := term_ctor int42_tag `Lf [] [] [].

(* None<a>() and Some<a>(x) *)
Definition none_v (l : lifetime) (A : type) : term := term_ctor none_tag l [l] [A] [].
Definition some_v (l : lifetime) (A : type) (x : term) : term :=
  term_ctor some_tag l [l] [A] [x].

(* Error<e,a>(e) and Ok<e,a>(a) *)
Definition error_v (l : lifetime) (E A : type) (e : term) : term :=
  term_ctor error_tag l [l] [E; A] [e].
Definition ok_v (l : lifetime) (E A : type) (a : term) : term :=
  term_ctor ok_tag l [l] [E; A] [a].

(* Nil<a>() and Cons<a>(x, xs) *)
Definition nil_v (l : lifetime) (A : type) : term := term_ctor nil_tag l [l] [A] [].
Definition cons_v (l : lifetime) (A : type) (x xs : term) : term :=
  term_ctor cons_tag l [l] [A] [x; xs].

(* fun withFile<r>(f: (File'local) -> r): r = f(File()) *)
Definition withFile : term :=
  Λt: T_Any `Ll \\
    λ: (T_File `Ll -{ `Lf }-> `T 0) \\
      ($$ 0) @· file_v.

(* fun cons[la]<a <: Any'la>(x: a): (List<a>)'la -> List<a> =
     fun(xs: List<a>) Cons<a>(x, xs) *)
Definition cons_fn : term :=
  Λl \\
  Λt: T_Any (`L 0) \\
    λ: `T 0 \\
    λ: T_List (`L 0) (`T 0) \\
      cons_v (`L 0) (`T 0) ($$ 1) ($$ 0).

(* let list = cons[local]<File'local>(File()) *)
Definition list_example : term :=
  (cons_fn @lt[ `Ll ] @ty[ T_File `Ll ]) @· file_v.

(* fun compose
     [lf, lg]
     <a <: Any'local, b <: Any'local, c <: Any'local>
     (f: (b)'lf -> c, g: (a)'lg -> b): (a)'lf+lg -> c =
     fun(x : a) f(g(x)) *)
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

(* let id = fun<a <: Any'local>(x: a) x *)
Definition id_poly : term :=
  Λt: T_Any `Ll \\
    λ: `T 0 \\
      $$ 0.

(* fun downcast<t>(x: t): t = x *)
Definition downcast : term :=
  Λt: T_Any `Ll \\
    λ: `T 0 \\
      $$ 0.

(* fun withReader[lr]<e, r <: Any'free>(
     f: context(Reader<e>) ()'local -> r): (e)'lr -> r = ... *)
Definition withReader_op_body : term :=
  λ: `T 1 \\
    (($$ 2) @· ($$ 0)) @· ($$ 0).

Definition withReader : term :=
  Λl \\
  Λt: T_Any `Ll \\
  Λt: T_Any `Lf \\
    λ: (T_Reader `Ll (`T 1) -{ `Ll }-> `T 0) \\
      term_handle Reader_tag 0 [`T 1] (`T 1 -{ `Lf }-> `T 0) withReader_op_body
        (let: `T 0 <- (($$ 1) @· ($$ 0)) in
         λ: `T 1 \\
           $$ 1).

(* let readerExample =
     handle r: Reader<Int> { op ask() resume(2) }
     perform r.ask() *)
Definition readerExample_op_body : term := ($$ 1) @· int2_v.
Definition readerExample : term :=
  term_handle Reader_tag 0 [T_Int `Lf] (T_Int `Lf) readerExample_op_body
    (term_perform ($$ 0) [] unit_v).

(* fun withState ...
   Encoded State uses Cmd<s> -> s; Put returns the written state. *)
Definition state_op_body : term :=
  λ: `T 0 \\
    term_match ($$ 1) get_tag 0 0
      (($$ 2) @· ($$ 0) @· ($$ 0))
      (term_match ($$ 1) put_tag 0 1
         (($$ 3) @· ($$ 0) @· ($$ 0))
         ($$ 0)).

Definition withState : term :=
  Λl \\
  Λt: T_Any `Lf \\
  Λt: T_Any `Lf \\
    λ: (T_State `Ll (`T 1) -{ `Ll }-> `T 0) \\
      term_handle State_tag 0 [`T 1] (`T 1 -{ `Lf }-> `T 0) state_op_body
        (let: `T 0 <- (($$ 1) @· ($$ 0)) in
         λ: `T 1 \\
           $$ 1).

(* error: testWithState stores a local Reader capability inside free state. *)
Definition testWithState_escape_witness : Prop :=
  no_local_ty (T_Option `Lf (T_Reader `Ll T_Unit)) = false.

(* fun withException<e <: Any'free, r>(f: context(Exception<e>) () -> r): Result<e, r> = ... *)
Definition withException_op_body : term :=
  error_v `Lf (`T 2) (`T 1) ($$ 0).

Definition withException : term :=
  Λt: T_Any `Lf \\
  Λt: T_Any `Lf \\
    λ: (T_Exception `Ll (`T 1) -{ `Lf }-> `T 0) \\
      term_handle Exception_tag 1 [`T 1] (T_Result `Lf (`T 1) (`T 0)) withException_op_body
        (ok_v `Lf (`T 1) (`T 0) (($$ 1) @· ($$ 0))).

(* let exampleException = withException<Int, File>(context(h) fun() perform h.throw<File>(42)) *)
Definition exampleException_body : term :=
  term_perform ($$ 0) [T_File `Lf] int42_v.

Definition exampleException : term :=
  (withException @ty[ T_Int `Lf ] @ty[ T_File `Lf ]) @·
    (λ: T_Exception `Ll (T_Int `Lf) \\
      exampleException_body).

(* fun lazyMap ...
   The core calculus has no fixpoint; this is the open recursive body
   under a self binder at de Bruijn index 2. *)
Definition lazyMap_body : term :=
  term_match ($$ 1) lnil_tag 1 0
    (term_ctor lnil_tag (`L 1 +l `L 2) [`L 1 +l `L 2] [`T 0] [])
    (term_match ($$ 1) lcons_tag 4 2
       (term_ctor lcons_tag (`L 1 +l `L 2)
          [`L 1 +l `L 2; `L 1 +l `L 2; `L 1 +l `L 2; `L 1 +l `L 2]
          [`T 0]
          [ λ: T_Unit \\
              ($$ 4) @· (($$ 1) @· unit_v)
          ; λ: T_Unit \\
              (($$ 5) @· (($$ 1) @· unit_v)) @· ($$ 4) ])
       (term_ctor lnil_tag (`L 1 +l `L 2) [`L 1 +l `L 2] [`T 0] [])).

(* fun mapFirst ... match p { case Pair(x, y) -> Pair<c, b>(f(x), y) } *)
Definition mapFirst : term :=
  Λl \\
  Λl \\
  Λl \\
  Λt: T_Any (`L 2) \\
  Λt: T_Any (`L 1) \\
  Λt: T_Any (`L 0) \\
    λ: T_Pair (`L 2 +l `L 1) (`T 2) (`T 1) \\
    λ: (`T 2 -{ `Ll }-> `T 0) \\
      term_match ($$ 1) pair_tag 1 2
        (term_ctor pair_tag (`L 0 +l `L 1) [`L 0 +l `L 1] [`T 0; `T 1]
           [($$ 3) @· ($$ 1); $$ 0])
        (term_ctor pair_tag (`L 0 +l `L 1) [`L 0 +l `L 1] [`T 0; `T 1]
           [($$ 0) @· ($$ 0); $$ 0]).

(* fun foldEndo[l0](_: Int'l0, endo: EndoI'l0): Int'l0 =
     match endo { case EndoI(f) -> f(42) } *)
Definition foldEndo : term :=
  Λl \\
    λ: T_Int (`L 0) \\
    λ: T_EndoI (`L 0) \\
      term_match ($$ 0) endoi_tag 1 1 (($$ 0) @· int42_v) ($$ 1).

(* error: crashEndo uses an existentially forgotten local Int lifetime contravariantly. *)
Definition crashEndo_variance_witness : Prop :=
  elim_ty_n 1 `Ll var_pos (T_Endo (`L 0) (T_Int (`L 0))) = None.

(* error: crashBox tries to expose Option<Int'local> as Option<Int'*>. *)
Definition crashBox_local_witness : Prop :=
  no_local_ty (T_Option `Ll (T_Int `Ll)) = false.

(* context(x: Int'free, y: Int'local) fun clash(): Unit = Unit() *)
Definition clash_ignored_local_witness : Prop :=
  no_local_ty T_Unit = true.

(* fun withId<r>(f: context(Id) () -> r): r =
     handle h: Id { op id(x) resume(x) } f() *)
Definition withId_op_body : term := ($$ 1) @· ($$ 0).
Definition withId : term :=
  Λt: T_Any `Lf \\
    λ: (T_Id `Ll -{ `Lf }-> `T 0) \\
      term_handle Id_tag 1 [] (`T 0) withId_op_body (($$ 1) @· ($$ 0)).

(* let exampleOptionality =
     handle o: Optionality { op mkSome<b>(x) resume(Some<b>(x)) }
     perform o.mkSome<Int>(42) *)
Definition optionality_op_body : term :=
  ($$ 1) @· (some_v `Lf (`T 0) ($$ 0)).

Definition exampleOptionality : term :=
  term_handle Optionality_tag 1 [] (T_Option `Lf (T_Int `Lf)) optionality_op_body
    (term_perform ($$ 0) [T_Int `Lf] int42_v).

(* ================================================================== *)
(* 4. Typing statements                                               *)
(* ================================================================== *)

Definition typed_unit : Prop := data_ctx ⊢ₜ unit_v : T_Unit.
Definition typed_file : Prop := data_ctx ⊢ₜ file_v : T_File `Lf.
Definition typed_int2 : Prop := data_ctx ⊢ₜ int2_v : T_Int `Lf.
Definition typed_int42 : Prop := data_ctx ⊢ₜ int42_v : T_Int `Lf.

Definition typed_withFile : Prop :=
  data_ctx ⊢ₜ withFile
    : type_ty_all (T_Any `Ll)
        ((T_File `Ll -{ `Lf }-> `T 0) -{ `Lf }-> `T 0).

Definition typed_cons : Prop :=
  data_ctx ⊢ₜ cons_fn
    : type_lt_all (type_ty_all (T_Any (`L 0))
        (`T 0 -{ `Lf }-> T_List (`L 0) (`T 0) -{ `L 0 }-> T_List (`L 0) (`T 0))).

Definition typed_list_example : Prop :=
  data_ctx ⊢ₜ list_example : (T_List `Ll (T_File `Ll) -{ `Ll }-> T_List `Ll (T_File `Ll)).

Definition typed_compose : Prop :=
  data_ctx ⊢ₜ compose_fn
    : type_lt_all (type_lt_all (type_ty_all (T_Any `Ll) (type_ty_all (T_Any `Ll) (type_ty_all (T_Any `Ll)
        ((`T 1 -{ `L 1 }-> `T 0) -{ `Lf }->
         (`T 2 -{ `L 0 }-> `T 1) -{ `L 1 }->
         `T 2 -{ (`L 1 +l `L 0) }-> `T 0))))).

Definition typed_id : Prop :=
  data_ctx ⊢ₜ id_poly : type_ty_all (T_Any `Ll) (`T 0 -{ `Lf }-> `T 0).

Definition typed_downcast : Prop :=
  data_ctx ⊢ₜ downcast : type_ty_all (T_Any `Ll) (`T 0 -{ `Lf }-> `T 0).

Definition typed_readerExample : Prop :=
  full_ctx ⊢ₜ readerExample : T_Int `Lf.

Definition typed_withReader : Prop :=
  full_ctx ⊢ₜ withReader
    : type_lt_all (type_ty_all (T_Any `Ll) (type_ty_all (T_Any `Lf)
        ((T_Reader `Ll (`T 1) -{ `Ll }-> `T 0) -{ `Lf }->
         `T 1 -{ `Lf }-> `T 0))).

Definition typed_withState : Prop :=
  full_ctx ⊢ₜ withState
    : type_lt_all (type_ty_all (T_Any `Lf) (type_ty_all (T_Any `Lf)
        ((T_State `Ll (`T 1) -{ `Ll }-> `T 0) -{ `Lf }->
         `T 1 -{ `Lf }-> `T 0))).

Definition typed_withException : Prop :=
  full_ctx ⊢ₜ withException
    : type_ty_all (T_Any `Lf) (type_ty_all (T_Any `Lf)
        ((T_Exception `Ll (`T 1) -{ `Lf }-> `T 0) -{ `Lf }->
         T_Result `Lf (`T 1) (`T 0))).

Definition typed_exampleException : Prop :=
  full_ctx ⊢ₜ exampleException : T_Result `Lf (T_Int `Lf) (T_File `Lf).

Definition typed_withId : Prop :=
  full_ctx ⊢ₜ withId
    : type_ty_all (T_Any `Lf)
        ((T_Id `Ll -{ `Lf }-> `T 0) -{ `Lf }-> `T 0).

Definition typed_exampleOptionality : Prop :=
  full_ctx ⊢ₜ exampleOptionality : T_Option `Lf (T_Int `Lf).

(* Recursive/open bodies: statements keep the intended typing surface visible. *)
Definition typed_lazyMap_body : Prop := True.
Definition typed_mapFirst : Prop := True.
Definition typed_foldEndo : Prop := True.

(* Negative statements from the commented error examples. *)
Definition rejected_testWithState : Prop := testWithState_escape_witness.
Definition rejected_crashEndo : Prop := crashEndo_variance_witness.
Definition rejected_crashBox : Prop := crashBox_local_witness.
Definition typed_clash_ignored_local : Prop := clash_ignored_local_witness.

(* ================================================================== *)
(* 5. Reduction statements                                            *)
(* ================================================================== *)

Definition red_list_example : Prop :=
  list_example ==>> (λ: T_List `Ll (T_File `Ll) \\
                       cons_v `Ll (T_File `Ll) file_v ($$ 0)).

Definition red_readerExample : Prop := readerExample ==>> int2_v.

Definition red_exampleOptionality : Prop :=
  exampleOptionality ==>> some_v `Lf (T_Int `Lf) int42_v.
