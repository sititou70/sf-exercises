Require Import Unicode.Utf8.
Require Import commons.

(********************************
  単純型付きラムダ計算
*********************************)

Module STLC.
  (* -----
    構文
  -------- *)

  Inductive id : Type :=
    Id : nat → id.

  Inductive ty : Type :=
    | ty_Bool : ty
    | ty_arrow : ty → ty → ty.
  
  Inductive tm : Type :=
    | tm_var : id → tm
    | tm_app : tm → tm → tm
    | tm_abs : id → ty → tm → tm
    | tm_true : tm
    | tm_false : tm
    | tm_if : tm → tm → tm → tm.

  Tactic Notation "tm_cases" tactic(first) ident(c) :=
    first;
    [ 
        Case_aux c "tm_var"
      | Case_aux c "tm_app"
      | Case_aux c "tm_abs"
      | Case_aux c "tm_true"
      | Case_aux c "tm_false"
      | Case_aux c "tm_if"
    ].
  
  Notation a := (Id 0).
  Notation b := (Id 1).
  Notation c := (Id 2).

  Notation idB :=
    (tm_abs a ty_Bool (tm_var a)).

  Notation idBB :=
    (tm_abs a (ty_arrow ty_Bool ty_Bool) (tm_var a)).

  Notation idBBBB :=
    (tm_abs a (ty_arrow (ty_arrow ty_Bool ty_Bool)
                        (ty_arrow ty_Bool ty_Bool))
              (tm_var a)).

  Notation k := (tm_abs a ty_Bool (tm_abs b ty_Bool (tm_var a))).

  (* -----
    操作的意味論
  -------- *)
  (* 値 *)
  Inductive value : tm → Prop :=
    | v_abs :
      ∀ (x : id) (T : ty) (t : tm),
      value (tm_abs x T t)
    | t_true :
      value tm_true
    | t_false :
      value tm_false.
  Hint Constructors value.

  (* 自由変数と置換 *)
  Fixpoint beq_nat (n m : nat) : bool :=
    match n with
    | O =>
      match m with
      | O => true
      | S m' => false
      end
    | S n' =>
      match m with
      | O => false
      | S m' => beq_nat n' m'
      end
    end.

  Definition beq_id id1 id2 :=
    match (id1, id2) with
      (Id n1, Id n2) => beq_nat n1 n2
    end.

  Fixpoint subst (s : tm) (x : id) (t : tm) : tm :=
    match t with
    | tm_var x' => if beq_id x x' then s else t
    | tm_abs x' T t1 => tm_abs x' T (if beq_id x x' then t1 else (subst s x t1))
    | tm_app t1 t2 => tm_app (subst s x t1) (subst s x t2)
    | tm_true => tm_true
    | tm_false => tm_false
    | tm_if t1 t2 t3 => tm_if (subst s x t1) (subst s x t2) (subst s x t3)
    end.

  Reserved Notation "t1 '==>' t2" (at level 40).
  Inductive step : tm → tm → Prop :=
    | ST_AppAbs :
      ∀ (x : id) (T : ty) (t12 : tm) (v2 : tm),
      value v2 →
      (tm_app (tm_abs x T t12) v2) ==> (subst v2 x t12)
    | ST_App1 : ∀ t1 t1' t2,
          t1 ==> t1' →
          tm_app t1 t2 ==> tm_app t1' t2
    | ST_App2 : ∀ v1 t2 t2',
          value v1 →
          t2 ==> t2' →
          tm_app v1 t2 ==> tm_app v1 t2'
    | ST_IfTrue : ∀ t1 t2,
        (tm_if tm_true t1 t2) ==> t1
    | ST_IfFalse : ∀ t1 t2,
        (tm_if tm_false t1 t2) ==> t2
    | ST_If : ∀ t1 t1' t2 t3,
        t1 ==> t1' →
        (tm_if t1 t2 t3) ==> (tm_if t1' t2 t3)
  where "t1 '==>' t2" := (step t1 t2).

  Tactic Notation "step_cases" tactic(first) ident(c) :=
    first;
    [
        Case_aux c "ST_AppAbs"
      | Case_aux c "ST_App1"
      | Case_aux c "ST_App2"
      | Case_aux c "ST_IfTrue"
      | Case_aux c "ST_IfFalse"
      | Case_aux c "ST_If"
    ].

  Definition relation (X : Type) := X → X → Prop.
  Inductive refl_step_closure (X : Type) (R : relation X): X → X → Prop :=
    | rsc_refl :
      ∀ (x : X),
      refl_step_closure X R x x
    | rsc_step :
      ∀ (x y z : X),
      R x y →
      refl_step_closure X R y z →
      refl_step_closure X R x z.
  Notation stepmany := (refl_step_closure step).
  Notation "t1 '==>*' t2" := (stepmany t1 t2) (at level 40).

  Hint Constructors step.
End STLC.
