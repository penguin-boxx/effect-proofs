Definition name := nat.

Inductive term : Set := 
  | term_var : name -> term
  | term_app : term -> term -> term
  | term_abs : (name -> term) -> term.

Example term_id : term := term_abs (fun x => term_var x).

Example term_composition : term := 
  term_abs (fun f => 
  term_abs (fun g => 
  term_abs (fun x => term_app (term_var f) (term_app (term_var g) (term_var x))))).

Inductive type : Set :=
  | type_var : name -> type
  | type_arrow : type -> type -> type.

Fixpoint subst (x : name) (new : term) (t : term) : term :=
  match t with
  | term_var y => if Nat.eqb x y then new else t
  | term_app t1 t2 => term_app (subst x new t1) (subst x new t2)
  | term_abs f => term_abs (fun y => if Nat.eqb x y then f y else subst x new (f y))
  end.

Inductive step : term -> term -> Prop :=
  | step_beta : forall f g x,
      step (term_app (term_abs f) g) (subst x g (f x))
  | step_app1 : forall t1 t1' t2,
      step t1 t1' ->
      step (term_app t1 t2) (term_app t1' t2)
  | step_app2 : forall t1 t2 t2',
      step t2 t2' ->
      step (term_app t1 t2) (term_app t1 t2')
  | step_abs : forall f f',
      (forall x, step (f x) (f' x)) ->
      step (term_abs f) (term_abs f').
