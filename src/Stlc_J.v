Require Import Unicode.Utf8.
Require Import commons.
Require Import Basics_J.
Require Import Arith.

(********************************
  単純型付きラムダ計算
*********************************)

Module STLC.
  (* -----
    構文
  -------- *)

  Inductive id : Type :=
    Id : nat -> id.

  Inductive ty : Type :=
    | ty_Bool : ty
    | ty_arrow : ty -> ty -> ty.
  
  Inductive tm : Type :=
    | tm_var : id -> tm
    | tm_app : tm -> tm -> tm
    | tm_abs : id -> ty -> tm -> tm
    | tm_true : tm
    | tm_false : tm
    | tm_if : tm -> tm -> tm -> tm.

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
  Inductive value : tm -> Prop :=
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

  (* 簡約 *)
  Reserved Notation "t1 '==>' t2" (at level 40).
  Inductive step : tm -> tm -> Prop :=
    | ST_AppAbs :
      ∀ (x : id) (T : ty) (t12 : tm) (v2 : tm),
      value v2 ->
      (tm_app (tm_abs x T t12) v2) ==> (subst v2 x t12)
    | ST_App1 :
      ∀ t1 t1' t2,
      t1 ==> t1' ->
      tm_app t1 t2 ==> tm_app t1' t2
    | ST_App2 :
      ∀ v1 t2 t2',
      value v1 ->
      t2 ==> t2' ->
      tm_app v1 t2 ==> tm_app v1 t2'
    | ST_IfTrue :
      ∀ t1 t2,
      (tm_if tm_true t1 t2) ==> t1
    | ST_IfFalse :
      ∀ t1 t2,
      (tm_if tm_false t1 t2) ==> t2
    | ST_If :
      ∀ t1 t1' t2 t3,
      t1 ==> t1' ->
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

  Definition relation (X : Type) := X -> X -> Prop.
  Inductive refl_step_closure {X : Type} (R: relation X): X -> X -> Prop :=
    | rsc_refl :
      ∀ (x : X),
      refl_step_closure R x x
    | rsc_step :
      ∀ (x y z : X),
      R x y ->
      refl_step_closure R y z ->
      refl_step_closure R x z.
  Notation stepmany := (refl_step_closure step).
  Notation "t1 '==>*' t2" := (stepmany t1 t2) (at level 40).

  Hint Constructors step.

  (* 例 *)
  Lemma step_example1 :
    (tm_app idBB idB) ==>* idB.
  Proof.
    eapply rsc_step.
      apply ST_AppAbs.
      apply v_abs.
    simpl.
    apply rsc_refl.
  Qed.

  (* Lemma step_example1' :
    (tm_app idBB idB) ==>* idB.
  Proof. normalize. Qed. *)

  Lemma step_example2 :
    (tm_app idBB (tm_app idBB idB)) ==>* idB.
  Proof.
    eapply rsc_step.
      apply ST_App2. auto.
      apply ST_AppAbs. auto.
    eapply rsc_step.
      apply ST_AppAbs. simpl. auto.
    simpl. apply rsc_refl.  
  Qed.

  (* 練習問題: ★★ (step_example3) *)
  (* normalizeを動作させられなかったため、使用しない方法だけ示す。 *)
  Lemma step_example3 :
    (tm_app (tm_app idBBBB idBB) idB) ==>* idB.
  Proof.
    eapply rsc_step.
    apply ST_App1.
    apply ST_AppAbs.
    auto.
    simpl.
    eapply rsc_step.
    apply ST_AppAbs.
    auto.
    simpl.
    apply rsc_refl.
  Qed.

  (* -----
    型付け
  -------- *)
  
  (* コンテキスト *)
  Definition partial_map (A : Type) := id -> option A.

  Definition context := partial_map ty.

  Theorem beq_id_refl : ∀ i,
    true = beq_id i i.
  Proof.
    intros. destruct i.
    apply beq_nat_refl. Qed.

  Module Context.
    Definition empty {A : Type} : partial_map A := (fun _ => None).

    Definition extend {A : Type} (Γ : partial_map A) (x : id) (T : A) :=
      fun x' => if beq_id x x' then Some T else Γ x'.

    Lemma extend_eq :
      ∀ A (ctxt : partial_map A) x T,
      (extend ctxt x T) x = Some T.
    Proof.
      intros. unfold extend. rewrite <- beq_id_refl. auto.
    Qed.

    Lemma extend_neq :
      ∀ A (ctxt : partial_map A) x1 T x2,
      beq_id x2 x1 = false ->
      (extend ctxt x2 T) x1 = ctxt x1.
    Proof.
      intros. unfold extend. rewrite H. auto.
    Qed.
  End Context.

  (* 型付け関係 *)
  Inductive has_type : context -> tm -> ty -> Prop :=
    | T_Var :
      ∀ Γ x T,
      Γ x = Some T ->
      has_type Γ (tm_var x) T
    | T_Abs :
      ∀ Γ x T11 T12 t12,
      has_type (Context.extend Γ x T11) t12 T12 ->
      has_type Γ (tm_abs x T11 t12) (ty_arrow T11 T12)
    | T_App :
      ∀ T11 T12 Γ t1 t2,
      has_type Γ t1 (ty_arrow T11 T12) ->
      has_type Γ t2 T11 ->
      has_type Γ (tm_app t1 t2) T12
    | T_True :
      ∀ Γ,
      has_type Γ tm_true ty_Bool
    | T_False :
      ∀ Γ,
      has_type Γ tm_false ty_Bool
    | T_If :
      ∀ t1 t2 t3 T Γ,
      has_type Γ t1 ty_Bool ->
      has_type Γ t2 T ->
      has_type Γ t3 T ->
      has_type Γ (tm_if t1 t2 t3) T.

  Tactic Notation "has_type_cases" tactic(first) ident(c) :=
    first;
    [
        Case_aux c "T_Var"
      | Case_aux c "T_Abs"  
      | Case_aux c "T_App"
      | Case_aux c "T_True"
      | Case_aux c "T_False"
      | Case_aux c "T_If"
    ].

  Hint Constructors has_type.

  (* 例 *)
  Example typing_example_1 :
    has_type Context.empty (tm_abs a ty_Bool (tm_var a)) (ty_arrow ty_Bool ty_Bool).
  Proof.
    apply T_Abs. apply T_Var. reflexivity.
  Qed.
  
  Example typing_example_1' :
    has_type Context.empty (tm_abs a ty_Bool (tm_var a)) (ty_arrow ty_Bool ty_Bool).
  Proof.
    auto.
  Qed.

  Hint Unfold beq_id beq_nat Context.extend.

  Example typing_example_2 :
    has_type
      Context.empty
      (tm_abs
        a
        ty_Bool
        (tm_abs
          b
          (ty_arrow ty_Bool ty_Bool)
          (tm_app
            (tm_var b)
            (tm_app
              (tm_var b)
              (tm_var a)
            )
          )
        )
      )
      (ty_arrow
        ty_Bool
        (ty_arrow
          (ty_arrow
            ty_Bool
            ty_Bool
          )
          ty_Bool
        )
      ).
  Proof with auto using Context.extend_eq.
    apply T_Abs.
    apply T_Abs.
    eapply T_App. apply T_Var...
    eapply T_App. apply T_Var...
    apply T_Var...
  Qed.

  (* 練習問題: ★★, optional *)
  Example typing_example_2_full :
    has_type
      Context.empty
      (tm_abs
        a
        ty_Bool
        (tm_abs
          b
          (ty_arrow ty_Bool ty_Bool)
          (tm_app
            (tm_var b)
            (tm_app (tm_var b) (tm_var a))
          )
        )
      )
      (ty_arrow
        ty_Bool
        (ty_arrow
          (ty_arrow
            ty_Bool
            ty_Bool
          )
          ty_Bool
        )
      ).
  Proof.
    apply T_Abs.
    apply T_Abs.
    eapply T_App.
      apply T_Var.
      apply Context.extend_eq.

      eapply T_App.
        apply T_Var.
        apply Context.extend_eq.

        apply T_Var.
        unfold Context.extend.
        simpl.
        reflexivity.
  Qed.

  (* 練習問題: ★★ (typing_example_3) *)
  Example typing_example_3 :
    ∃ T,
      has_type
        Context.empty
        (tm_abs
          a
          (ty_arrow ty_Bool ty_Bool)
          (tm_abs
            b
            (ty_arrow ty_Bool ty_Bool)
            (tm_abs
              c
              ty_Bool
              (tm_app
                (tm_var b)
                (tm_app
                  (tm_var a)
                  (tm_var c)
                )
              )
            )
          )
        )
        T.
  Proof with auto.
    apply ex_intro with (ty_arrow (ty_arrow ty_Bool ty_Bool) (ty_arrow (ty_arrow ty_Bool ty_Bool) (ty_arrow ty_Bool ty_Bool))).
    apply T_Abs.
    apply T_Abs.
    apply T_Abs.
    eapply T_App.
      apply T_Var.
      unfold Context.extend.
      simpl...

      eapply T_App; 
        apply T_Var;
        unfold Context.extend;
        simpl...
  Qed.

  Example typing_nonexample_1 :
    ~ ∃ T,
        has_type Context.empty
          (tm_abs a ty_Bool
              (tm_abs b ty_Bool
                (tm_app (tm_var a) (tm_var b))))
          T.
  Proof.
    intros C. destruct C.
    inversion H. subst. clear H.
    inversion H5. subst. clear H5.
    inversion H4. subst. clear H4.
    inversion H2. subst. clear H2.
    inversion H5. subst. clear H5.
    inversion H1.
  Qed.
  
  (* 練習問題: ★★★ (typing_nonexample_3) *)
  Theorem impossible_arrow_self_ref:
    forall T1 T2,
    ~ ty_arrow T1 T2 = T1.
  Proof.
    unfold not.
    intros.
    induction T1.
    SSCase "T1: Bool".
      inversion H.
    SSCase "T1: arrow".
      inversion H.
      apply IHT1_1.
      rewrite H2.
      apply H1.
  Qed.

  Example typing_nonexample_3 :
    ~ (∃ S, ∃ T,
      has_type
        Context.empty
        (tm_abs a S
          (tm_app
            (tm_var a)
            (tm_var a)
          )
        )
        T
    ).
  Proof.
    intros E1.
    destruct E1.
    destruct H.
    destruct x.
    Case "x: Bool".
      inversion H.
      subst.
      clear H.
      inversion H5.
      subst.
      clear H5.
      inversion H2.
      subst.
      clear H2.
      inversion H1.
    Case "x: arrow".
      inversion H.
      subst.
      clear H.
      inversion H5.
      subst.
      clear H5.
      inversion H2.
      subst.
      clear H2.
      inversion H4.
      subst.
      clear H4.
      rewrite H1 in H2.
      inversion H2.
      apply impossible_arrow_self_ref in H0.
      apply H0.
  Qed.

  (* 練習問題: ★ (typing_statements) *)
  (*
    - b:Bool |- \a:Bool. a : Bool->Bool
    - ∃ T, empty |- (\b:Bool->Bool. \a:Bool. b a) : T
    - ∃ S, a:S |- (\b:Bool->Bool. b) a : S
  *)

  (* 練習問題: ★, optional (more_typing_statements) *)
  (*
  ∃ T, empty |- (\b:B->B->B. \a:B, b a) : T
    T = B->B
  ∃ T, empty |- (\a:A->B, \b:B->C, \c:A, b (a c)):T
    T = C
  ∃ S, ∃ U, ∃ T, a:S, b:U |- \c:A. a (b c) : T
    forall S1 S2,
      U = A->S1
      S = S1->S2
      T = A->S2
  ∃ S, ∃ T, a:S |- \b:A. a (a b) : T
    S = A->A
    T = A->A
  ∃ S, ∃ U, ∃ T, a:S |- a (\c:U. c a) : T
    証明できない
  *)

  (* -----
    性質
  -------- *)

  (* 自由な出現 *)
  Inductive appears_free_in : id -> tm -> Prop :=
    | afi_var :
      ∀ x,
      appears_free_in x (tm_var x)
    | afi_app1 :
      ∀ x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tm_app t1 t2)
    | afi_app2 :
      ∀ x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tm_app t1 t2)
    | afi_abs :
      ∀ x y T11 t12,
      y <> x ->
      appears_free_in x t12 ->
      appears_free_in x (tm_abs y T11 t12)
    | afi_if1 :
      ∀ x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tm_if t1 t2 t3)
    | afi_if2 :
      ∀ x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tm_if t1 t2 t3)
    | afi_if3 :
      ∀ x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tm_if t1 t2 t3).

  Tactic Notation "afi_cases" tactic(first) ident(c) :=
    first;
    [
        Case_aux c "afi_var"
      | Case_aux c "afi_app1"
      | Case_aux c "afi_app2"
      | Case_aux c "afi_abs"
      | Case_aux c "afi_if1"
      | Case_aux c "afi_if2"
      | Case_aux c "afi_if3"
    ].

  Hint Constructors appears_free_in.

  Definition closed (t : tm) :=
    ∀ x, ~ appears_free_in x t.
  
  (* 置換 *)
  Theorem not_eq_beq_false : ∀ n n' : nat,
    n <> n' ->
    beq_nat n n' = false.
  Proof.
  Admitted.

  Theorem not_eq_beq_id_false : ∀ i1 i2,
    i1 <> i2 -> beq_id i1 i2 = false.
  Proof.
    intros i1 i2 H.
    destruct i1. destruct i2.
    assert (n <> n0).
      intros C. subst. apply H. reflexivity.
    apply not_eq_beq_false. assumption. Qed.

  Lemma free_in_context :
    ∀ x t T Γ,
    appears_free_in x t ->
    has_type Γ t T ->
    ∃ T', Γ x = Some T'.
  Proof.
    intros. generalize dependent Γ. generalize dependent T.
    afi_cases (induction H) Case;
          intros; try solve [inversion H0; eauto].
    Case "afi_abs".
      inversion H1; subst.
      apply IHappears_free_in in H7.
      apply not_eq_beq_id_false in H.
      rewrite Context.extend_neq in H7; assumption.
  Qed.

  Corollary typable_empty__closed :
    ∀ t T,
    has_type Context.empty t T ->
    closed t.
  Proof.
    unfold closed.
    unfold not.
    intros.
    apply free_in_context with (T := T) (Γ := Context.empty) in H0.
      inversion H0.
      inversion H1.

      assumption.
  Qed.

  Definition beq_nat_false := fun n m => proj1 (Nat.eqb_neq n m).
  Theorem beq_id_false_not_eq : ∀ i1 i2,
    beq_id i1 i2 = false → i1 <> i2.
  Proof.
    Admitted.
  Lemma context_invariance :
    ∀ Γ Γ' t S,
    has_type Γ t S ->
    (∀ x, appears_free_in x t -> Γ x = Γ' x) ->
    has_type Γ' t S.
  Proof with eauto.
    intros.
    generalize dependent Γ'.
    has_type_cases (induction H) Case; intros; auto.
    Case "T_Var".
      apply T_Var. rewrite <- H0...
    Case "T_Abs".
      apply T_Abs.
      apply IHhas_type. intros x0 Hafi.
      unfold Context.extend. remember (beq_id x x0) as e. destruct e...
      apply H0.
      apply afi_abs.
      apply beq_id_false_not_eq.
      auto.
      auto.
    Case "T_App".
      apply T_App with T11...
  Qed.

  Theorem beq_id_eq : ∀ i1 i2,
    true = beq_id i1 i2 → i1 = i2.
  Proof.
    Admitted.
  Lemma substitution_preserves_typing :
    ∀ Γ x U v t T,
    has_type (Context.extend Γ x U) t T ->
    has_type Context.empty v U ->
    has_type Γ (subst v x t) T.
  Proof with eauto.
    intros Γ x U v t T Ht Hv.
    generalize dependent Γ. generalize dependent T.
    tm_cases (induction t) Case; intros T Γ H;
      inversion H; subst; simpl...
    Case "tm_var".
      rename i into y. remember (beq_id x y) as e. destruct e.
      SCase "x=y".
        apply beq_id_eq in Heqe. subst.
        rewrite Context.extend_eq in H2.
        inversion H2; subst. clear H2.
                    eapply context_invariance... intros x Hcontra.
        specialize (free_in_context _ _ T Context.empty Hcontra Hv) as tmp.
        destruct (free_in_context _ _ T Context.empty Hcontra) as [T' HT']...
        inversion HT'.
      SCase "x<>y".
        apply T_Var. rewrite Context.extend_neq in H2...
    Case "tm_abs".
      rename i into y. apply T_Abs.
      remember (beq_id x y) as e. destruct e.
      SCase "x=y".
        eapply context_invariance...
        apply beq_id_eq in Heqe. subst.
        intros x Hafi. unfold Context.extend.
        destruct (beq_id y x)...
      SCase "x<>y".
        apply IHt. eapply context_invariance...
        intros z Hafi. unfold Context.extend.
        remember (beq_id y z) as e0. destruct e0...
        apply beq_id_eq in Heqe0. subst.
        rewrite <- Heqe...
  Qed.

  (* 保存 *)
  Theorem preservation :
    ∀ t t' T,
    has_type Context.empty t T ->
    t ==> t' ->
    has_type Context.empty t' T.
  Proof with eauto.
    remember (@Context.empty ty) as Γ.
    intros t t' T HT. generalize dependent t'.
    has_type_cases (induction HT) Case;
      intros t' HE; subst Γ; subst;
      try solve [inversion HE; subst; auto].
    Case "T_App".
      inversion HE; subst...
      SCase "ST_AppAbs".
        apply substitution_preserves_typing with T11...
        inversion HT1...
  Qed.

  (* 練習問題: ★★, recommended (subject_expansion_stlc) *)
  (* https://www.dcc.fc.up.pt/~sandra/Home/Material_files/TypedLambda.pdf *)
  (* 反例を示す。以下のtとt'について、 *)
  Definition subject_expansion_stlc_t :=
    (tm_app
      (tm_abs
        a
        (ty_arrow ty_Bool ty_Bool)
        (tm_abs
          b
          ty_Bool
          (tm_var b)
        )
      )
      (tm_abs
        c
        ty_Bool
        (tm_app
          (tm_var c)
          (tm_var c)
        )
      )
    ).
  Definition subject_expansion_stlc_t' :=
    (tm_abs
      b
      ty_Bool
      (tm_var b)
    ).

  (* t ==> t'であり、 *)
  Example subject_expansion_stlc_t__t':
    subject_expansion_stlc_t ==> subject_expansion_stlc_t'.
  Proof.
    apply ST_AppAbs.
    apply v_abs.
  Qed.

  (* has_type Context.empty t' Tであるが *)
  Example subject_expansion_stlc_has_type_t':
    exists T,
    has_type
      Context.empty
      subject_expansion_stlc_t'
      T.
  Proof.
    unfold subject_expansion_stlc_t'.
    apply ex_intro with (x := ty_arrow ty_Bool ty_Bool).
    eapply T_Abs.
    apply T_Var.
    auto.
  Qed.

  (* has_type Context.empty t Tでない *)
  Example subject_expansion_stlc_has_not_type_t :
    ~ (exists T,
      has_type
        Context.empty
        subject_expansion_stlc_t
        T
    ).
  Proof.
    unfold not.
    intros.
    inversion H. clear H.
    inversion H0. subst. clear H0.
    clear H3.
    inversion H5. subst. clear H5.
    inversion H4. subst. clear H4.
    inversion H2. subst. clear H2.
    inversion H5. subst. clear H5.
    rewrite H1 in H2. clear H1.
    inversion H2.
    apply impossible_arrow_self_ref in H0.
    assumption.
  Qed.

  (* 進行 *)
  Theorem progress : ∀ t T,
    has_type Context.empty t T →
    value t \/ ∃ t', t ==> t'.
  Proof with eauto.
    intros t T Ht.
    remember (@Context.empty ty) as Γ.
    has_type_cases (induction Ht) Case; subst Γ...
    Case "T_Var".
      inversion H.
    Case "T_App".
      right. destruct IHHt1...
      SCase "t1 is a value".
        destruct IHHt2...
        SSCase "t2 is also a value".
          inversion H; subst.
            apply ex_intro with (subst t2 x t)...
            inversion Ht1.
            inversion Ht1.
        SSCase "t2 steps".
          destruct H0 as [t2' Hstp]. apply ex_intro with (tm_app t1 t2')...
      SCase "t1 steps".
        destruct H as [t1' Hstp]. apply ex_intro with (tm_app t1' t2)...
    Case "T_If".
      right. destruct IHHt1...
      SCase "t1 is a value".
        inversion H; subst. inversion Ht1.
        SSCase "t1 = true". eauto.
        SSCase "t1 = false". eauto.
      SCase "t1 also steps".
        destruct H as [t1' Hstp]. apply ex_intro with (tm_if t1' t2 t3)...
  Qed.

  (* 練習問題: ★★★, optional (progress_from_term_ind) *)
  Theorem progress' :
    ∀ t T,
    has_type Context.empty t T →
    value t \/ exists t', t ==> t'.
  Proof.
    intros t.
    tm_cases (induction t) Case; intros T Ht; auto.
    Case "tm_var".
      inversion Ht.
      subst.
      inversion H1.
    Case "tm_app".
      inversion Ht.
      subst.
      specialize H2 as H3.
      apply IHt1 in H2.
      destruct H2.
      SCase "t1 is a value".
        apply IHt2 in H4.
        destruct H4.
        SSCase "t2 is a value".
          inversion H.
          SSSCase "t1: v_abs".
            right.
            apply ex_intro with (subst t2 x t).
            apply ST_AppAbs.
            assumption.
          SSSCase "t1: v_true".
            rewrite <- H1 in H3.
            inversion H3.
          SSSCase "t1: v_false".
            rewrite <- H1 in H3.
            inversion H3.
        SSCase "t2 ==> t2'".
          right.
          inversion H0 as [t2'].
          apply ex_intro with (tm_app t1 t2').
          apply ST_App2.
            assumption.
            assumption.
      SCase "t1 ==> t1'".
        right.
        inversion H as [t1'].
        apply ex_intro with (tm_app t1' t2).
        apply ST_App1.
        assumption.
    Case "tm_if".
      inversion  Ht.
      subst.
      specialize H3 as H4.
      apply IHt1 in H3.
      destruct H3.
      SCase "t1 is a value".
        inversion H.
        SSCase "t1: v_abs".
          rewrite <- H0 in H4.
          inversion H4.
        SSCase "t1: v_true".
          right.
          apply ex_intro with t2.
          apply ST_IfTrue.
        SSCase "t1: v_false".
          right.
          apply ex_intro with t3.
          apply ST_IfFalse.
      SCase "t1 ==> t1'".
        inversion H as [t1'].
        right.
        apply ex_intro with (tm_if t1' t2 t3).
        apply ST_If.
        assumption.
  Qed.

  (* 型の一意性 *)
  (* 練習問題: ★★★ (types_unique) *)
  Theorem types_unique :
    forall Γ t T T',
    has_type Γ t T ->
    has_type Γ t T' ->
    T = T'.
  Proof.
    intros Γ t T T' HTtT HTtT'.
    generalize dependent T'.
    has_type_cases (induction HTtT) Case.
    Case "T_Var".
      intros.
      inversion HTtT'.
      subst.
      rewrite H2 in H.
      inversion H.
      reflexivity.
    Case "T_Abs".
      intros.
      inversion HTtT'.
      subst.
      apply IHHTtT in H4.
      rewrite H4.
      reflexivity.
    Case "T_App".
      intros.
      inversion HTtT'.
      subst.
      apply IHHTtT1 in H2.
      inversion H2.
      reflexivity.
    Case "T_True".
      intros.
      inversion HTtT'.
      subst.
      reflexivity.
    Case "T_False".
      intros.
      inversion HTtT'.
      subst.
      reflexivity.
    Case "T_If".
      intros.
      inversion HTtT'.
      subst.
      apply IHHTtT2 in H5.
      assumption.
  Qed.

  (* -----
    さらなる練習問題
  -------- *)
  (* 練習問題: ★ (progress_preservation_statement) *)
  (*
    進行定理：型が付いた項は1ステップ評価できるか、値である。
      forall Gamma t T,
      has_type Gamma t T ->
      (exists t', t ==> t') \/ value t

    保存定理：項を評価しても型付けは変化しない。
      forall Gamma t t' T,
      has_type Gamma t T ->
      t ==> t' ->
      has_type Gamma t' T
  *)
  
  (* 練習問題: ★★, optional (stlc_variation1) *)
  (*
    stepの決定性：真のまま

    進行：偽に変わる
      項「if \x:bool. x then true else false」はBool型が付くが、1ステップ評価できず値でもない。

    保存：真のまま
  *)
  
  (* 練習問題: ★★ (stlc_variation2) *)
  (*
    stepの決定性：真のまま

    進行：偽に変わる
      項「(if true then (\x:Bool. x) else (\x:Bool. x)) true」はBool型が付くが、1ステップ評価できず値でもない。

    保存：真のまま
  *)
End STLC.

(********************************
  練習問題: 算術を持つSTLC
*********************************)
(* TODO *)

