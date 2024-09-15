Require Import Unicode.Utf8.
Require Import commons.
Require Import Arith.
Require Import Lia.
Require Import Imp_J.


(********************************
  振る舞い同値性
*********************************)

(* -----
  定義
-------- *)
Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st || st') <-> (c2 / st || st').

(* 練習問題: ★★, optional (pairs_equiv) *)
(* 
a: no。X = 1のとき、一方は無限ループになるが、他方は即座に停止する。
b: yes。両者は何もせず停止する。
*)

(* -----
  例
-------- *)
Theorem aequiv_example:
  aequiv (AMinus (AId X) (AId X)) (ANum 0).
Proof.
  intros st. simpl. lia.
Qed.

Theorem bequiv_example:
  bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue.
Proof.
  intros st. unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

Theorem skip_left:
  forall c,
  cequiv
     (SKIP; c)
     c.
Proof.
  intros c st st'.
  split; intros H.
  Case "->".
    inversion H. subst.
    inversion H2. subst.
    assumption.
  Case "<-".
    apply E_Seq with st.
    apply E_Skip.
    assumption.
Qed.

(* 練習問題: ★★ (skip_right) *)
Theorem skip_right:
  forall c,
  cequiv
    (c; SKIP)
    c.
Proof.
  unfold cequiv.
  intros.
  split; intros.
  Case "->".
    rename st' into st''.
    inversion H; subst.
    inversion H5; subst.
    assumption.
  Case "<-".
    apply E_Seq with (st' := st').
    assumption.
    apply E_Skip.
Qed.

Theorem IFB_true_simple :
  forall c1 c2,
  cequiv
    (IFB BTrue THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros c1 c2.
  split; intros H.
  Case "->".
    inversion H; subst. assumption. inversion H5.
  Case "<-".
    apply E_IfTrue. reflexivity. assumption.
Qed.

Theorem IFB_true :
  forall b c1 c2,
  bequiv b BTrue ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  Case "->".
    inversion H; subst.
    SCase "b evaluates to true".
      assumption.
    SCase "b evaluates to false (contradiction)".
      rewrite Hb in H5.
      inversion H5.
  Case "<-".
    apply E_IfTrue; try assumption.
    rewrite Hb. reflexivity.
Qed.

(* 練習問題: ★★, recommended (IFB_false) *)
Theorem IFB_false :
  forall b c1 c2,
  bequiv b BFalse ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c2.
Proof.
  intros b c1 c2 Hbeq.

  unfold bequiv in Hbeq.
  simpl in Hbeq.

  split; intros.
  Case "->".
    inversion H; subst.
    SCase "b evaluates to true (contradiction)".
      rewrite (Hbeq st) in H5.
      inversion H5.
    SCase "b evaluates to false".
      assumption.
  Case "<-".
    apply E_IfFalse.
    apply (Hbeq st).
    assumption.
Qed.

(* 練習問題: ★★★ (swap_if_branches) *)
Theorem swap_if_branches :
  forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  unfold cequiv.
  intros.
  split; intros.
  Case "->".
    inversion H; subst.
    SCase "beval st b = true".
      apply E_IfFalse.
      simpl.
      apply Bool.negb_false_iff.
      assumption.
      assumption.
    SCase "beval st b = false".
      apply E_IfTrue.
      simpl.
      apply Bool.negb_true_iff.
      assumption.
      assumption.
  Case "<-".
    inversion H; subst; simpl in H5.
    SCase "beval st (BNot b) = true".
      apply Bool.negb_true_iff in H5.
      apply E_IfFalse.
      assumption.
      assumption.
    SCase "beval st (BNot b) = false".
      apply Bool.negb_false_iff in H5.
      apply E_IfTrue.
      assumption.
      assumption.
Qed.

Theorem WHILE_false :
  forall b c,
  bequiv b BFalse ->
  cequiv
    (WHILE b DO c END)
    SKIP.
Proof.
  intros b c Hb. split; intros H.
  Case "->".
    inversion H; subst.
    SCase "E_WhileEnd".
      apply E_Skip.
    SCase "E_WhileLoop".
      rewrite Hb in H2. inversion H2.
  Case "<-".
    inversion H; subst.
    apply E_WhileEnd.
    rewrite Hb.
    reflexivity.
Qed.

(* 練習問題: ★★ (WHILE_false_informal) *)
(*
定理：bがBFalseと同値ならば、WHILE b DO c ENDはSKIPと同値である。

証明：
  (WHILE b DO c END) / st || st' -> SKIP / st || st'を示す：
    仮定である(WHILE b DO c END) / st || st'で使用された評価規則で場合分けする：
      E_WhileEndの場合：
        評価規則の結論より、(WHILE b DO c END) / st || stであるため、st = stである。
        したがって、SKIP / st || stを示せばよく、これはE_Skipより明らかである。
      E_WhileLoopの場合：
        評価規則の仮定より、beval st b = trueである。
        しかしこれは定理の仮定に矛盾するため、所望の結論は自明に満たされる。
  SKIP / st || st' -> (WHILE b DO c END) / st || st'を示す：
    仮定であるSKIP / st || st'で使用された評価規則で場合分けする：
      E_Skipの場合：
        評価規則の結論より、SKIP / st || stであるため、st = stである。
        したがって、(WHILE b DO c END) / st || stを示せば良く、定理の前提とE_WhileEnd規則によって成り立つ。
*)

Lemma WHILE_true_nonterm :
  forall b c st st',
  bequiv b BTrue ->
  ~( (WHILE b DO c END) / st || st' ).
Proof.
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw.
  ceval_cases (induction H) Case;
    inversion Heqcw; subst; clear Heqcw.
  Case "E_WhileEnd".
    rewrite Hb in H. inversion H.
  Case "E_WhileLoop".
    apply IHceval2. reflexivity.
Qed.

(* 練習問題: ★★, optional (WHILE_true_nonterm_informal) *)
(*
定理：bがBTrueと同値であり、(WHILE b DO c END) / st || st'ならば、矛盾である。

証明：
  (WHILE b DO c END) / st || st'について、cevalによる帰納法を適用する。

  E_WhileEndの場合：
    規則の仮定よりbeval st b1 = falseである。
    しかしこれは定理の前提と矛盾するため、所望の結論は自明に満たされる。

  E_WhileLoopの場合：
    帰納法の仮定より、「bがTrueと同値であり、(WHILE b1 DO c1 END) / st' || st''ならば、矛盾」である。
    定理の前提より、bはTrueと同値である。
    評価規則の仮定より、(WHILE b1 DO c1 END) / st' || st''である。
    したがって矛盾が示された。

  その他の場合：
    WHILEを結論としてないため矛盾する。
    したがって、所望の結論は自明に満たされる。
*)

(* 練習問題: ★★, recommended (WHILE_true) *)
Theorem WHILE_true :
  forall b c,
  bequiv b BTrue ->
  cequiv
    (WHILE b DO c END)
    (WHILE BTrue DO SKIP END).
Proof.
  unfold bequiv, cequiv.
  intros b c Hbtrue st st'.
  simpl in Hbtrue.
  split; intros.
  Case "->".
    rename st' into st''.
    inversion H; subst.
    SCase "E_WhileEnd".
      rewrite (Hbtrue st'') in H4.
      inversion H4.
    SCase "E_WhileLoop".
      specialize (WHILE_true_nonterm _ c st st'' Hbtrue) as Hnoterm.
      apply Hnoterm in H.
      inversion H.
  Case "<-".
    specialize (WHILE_true_nonterm BTrue SKIP st st') as Hnoterm.
    apply Hnoterm in H.

    inversion H.

    unfold bequiv.
    intros.
    reflexivity.
Qed.

Theorem loop_unrolling :
  forall b c,
  cequiv
    (WHILE b DO c END)
    (IFB b THEN (c; WHILE b DO c END) ELSE SKIP FI).
Proof.
  intros b c st st'.
  split; intros Hce.
  Case "->".
    inversion Hce; subst.
    SCase "loop doesn't run".
      apply E_IfFalse. assumption. apply E_Skip.
    SCase "loop runs".
      apply E_IfTrue. assumption.
      apply E_Seq with (st' := st'0). assumption. assumption.
  Case "<-".
    inversion Hce; subst.
    SCase "loop runs".
      inversion H5; subst.
      apply E_WhileLoop with (st' := st'0).
      assumption. assumption. assumption.
    SCase "loop doesn't run".
      inversion H5; subst. apply E_WhileEnd. assumption.
Qed.

(* 練習問題: ★★, optional (seq_assoc) *)
Theorem seq_assoc :
  forall c1 c2 c3,
  cequiv ((c1;c2);c3) (c1;(c2;c3)).
Proof.
  unfold cequiv.
  intros.
  rename st' into st'''.
  split; intros.
  Case "->".
    inversion H; subst.
    rename st' into st''.
    inversion H2; subst.
    eauto using ceval.
  Case "<-".
    inversion H; subst.
    rename st' into st''.
    inversion H5; subst.
    eauto using ceval.
Qed.

Theorem identity_assignment_first_try :
  forall (X : Id.id),
  cequiv
    (X ::= AId X)
    SKIP.
Proof.
  intros. split; intro H.
    Case "->".
      inversion H; subst. simpl.
      replace (update st X (st X)) with st.
      constructor.
Admitted.

Axiom functional_extensionality :
  forall {X Y: Type} {f g : X -> Y},
  (forall (x: X), f x = g x) -> f = g.

Theorem identity_assignment :
  forall (X : Id.id),
  cequiv
    (X ::= AId X)
    SKIP.
Proof.
  intros. split; intro H.
    Case "->".
      inversion H; subst. simpl.
      replace (update st X (st X)) with st.
      constructor.
      apply functional_extensionality. intro.
      rewrite update_same; reflexivity.
    Case "<-".
      inversion H; subst.
      assert (st' = (update st' X (st' X))).
        apply functional_extensionality. intro.
        rewrite update_same; reflexivity.
      rewrite H0 at 2.
      constructor. reflexivity.
Qed.

(* 練習問題: ★★, recommended (assign_aequiv) *)
Theorem assign_aequiv :
  forall X e,
  aequiv (AId X) e ->
  cequiv SKIP (X ::= e).
Proof.
  unfold aequiv, cequiv.
  intros X e Hxeqe st st'.

  assert (Hst: st = update st X (aeval st e)).
  Case "Proof of assertion".
    apply functional_extensionality.
    intros.
    simpl in Hxeqe.
    rewrite <- Hxeqe.
    rewrite update_same.
    reflexivity.
    reflexivity.

  split; intros.
  Case "->".
    inversion H; subst.
    rename st' into st.
    rewrite Hst at 2.
    constructor.
    reflexivity.
  Case "<-".
    inversion H; subst.
    rewrite <- Hst.
    constructor.
Qed.

(********************************
  振る舞い同値の性質
*********************************)

(* -----
  振る舞い同値は同値関係である
-------- *)
Lemma refl_aequiv :
  forall (a : aexp), aequiv a a.
Proof.
  intros a st. reflexivity.
Qed.

Lemma sym_aequiv :
  forall (a1 a2 : aexp),
  aequiv a1 a2 ->
  aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H.
Qed.

Lemma trans_aequiv :
  forall (a1 a2 a3 : aexp),
  aequiv a1 a2 ->
  aequiv a2 a3 ->
  aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.
Qed.

Lemma refl_bequiv :
  forall (b : bexp), bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity.
Qed.

Lemma sym_bequiv :
  forall (b1 b2 : bexp),
  bequiv b1 b2 ->
  bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H.
Qed.

Lemma trans_bequiv :
  forall (b1 b2 b3 : bexp),
  bequiv b1 b2 ->
  bequiv b2 b3 ->
  bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.
Qed.

Lemma refl_cequiv :
  forall (c : com), cequiv c c.
Proof.
  unfold cequiv. intros c st st'. apply iff_refl.
Qed.

Lemma sym_cequiv :
  forall (c1 c2 : com),
  cequiv c1 c2 ->
  cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  assert (c1 / st || st' <-> c2 / st || st') as H'.
    SCase "Proof of assertion". apply H.
  apply iff_sym. assumption.
Qed.

Lemma iff_trans :
  forall (P1 P2 P3 : Prop),
  (P1 <-> P2) -> (P2 <-> P3) ->
  (P1 <-> P3).
Proof.
  intros P1 P2 P3 H12 H23.
  inversion H12. inversion H23.
  split; intros A.
    apply H1. apply H. apply A.
    apply H0. apply H2. apply A.
  Qed.

Lemma trans_cequiv :
  forall (c1 c2 c3 : com),
  cequiv c1 c2 ->
  cequiv c2 c3 ->
  cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  apply iff_trans with (c2 / st || st'). apply H12. apply H23.
Qed.

(* -----
  振る舞い同値は合同関係である
-------- *)
Theorem CAss_congruence :
  forall i a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss i a1) (CAss i a1').
Proof.
  intros i a1 a2 Heqv st st'.
  split; intros Hceval.
  Case "->".
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.
  Case "<-".
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.
Qed.

Theorem CWhile_congruence :
  forall b1 b1' c1 c1',
  bequiv b1 b1' ->
  cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  unfold bequiv,cequiv.
  intros b1 b1' c1 c1' Hb1e Hc1e st st'.
  split; intros Hce.
  Case "->".
    remember (WHILE b1 DO c1 END) as cwhile.
    induction Hce; inversion Heqcwhile; subst.
    SCase "E_WhileEnd".
      apply E_WhileEnd. rewrite <- Hb1e. apply H.
    SCase "E_WhileLoop".
      apply E_WhileLoop with (st' := st').
      SSCase "show loop runs". rewrite <- Hb1e. apply H.
      SSCase "body execution".
        apply (Hc1e st st'). apply Hce1.
      SSCase "subsequent loop execution".
        apply IHHce2. reflexivity.
  Case "<-".
    remember (WHILE b1' DO c1' END) as c'while.
    induction Hce; inversion Heqc'while; subst.
    SCase "E_WhileEnd".
      apply E_WhileEnd. rewrite -> Hb1e. apply H.
    SCase "E_WhileLoop".
      apply E_WhileLoop with (st' := st').
      SSCase "show loop runs". rewrite -> Hb1e. apply H.
      SSCase "body execution".
        apply (Hc1e st st'). apply Hce1.
      SSCase "subsequent loop execution".
        apply IHHce2. reflexivity.
Qed.

(* 練習問題: ★★★, optional (CSeq_congruence) *)
Theorem CSeq_congruence :
  forall c1 c1' c2 c2',
  cequiv c1 c1' ->
  cequiv c2 c2' ->
  cequiv (c1;c2) (c1';c2').
Proof.
  intros c1 c1' c2 c2' Hcequivc1 Hcequivc2.
  unfold cequiv.
  split; intros.
  Case "->".
    rename st' into st''.
    inversion H; subst.
    apply E_Seq with (st' := st').
    apply Hcequivc1.
    assumption.
    apply Hcequivc2.
    assumption.
  Case "<-".
    rename st' into st''.
    inversion H; subst.
    apply E_Seq with (st' := st').
    apply Hcequivc1.
    assumption.
    apply Hcequivc2.
    assumption.
Qed.

(* 練習問題: ★★★ (CIf_congruence) *)
Theorem CIf_congruence :
  forall b b' c1 c1' c2 c2',
  bequiv b b' ->
  cequiv c1 c1' ->
  cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
  unfold bequiv, cequiv.
  intros b b' c1 c1' c2 c2' Hbeq Hc1eq Hc2eq st st'.
  split; intros.
  Case "->".
    inversion H; subst.
    SCase "E_IfTrue".
      apply E_IfTrue.
      rewrite Hbeq in H5.
      assumption.
      apply Hc1eq.
      assumption.
    SCase "E_IfFalse".
      apply E_IfFalse.
      rewrite Hbeq in H5.
      assumption.
      apply Hc2eq.
      assumption.
  Case "<-".
    inversion H; subst.
    SCase "E_IfTrue".
      apply E_IfTrue.
      rewrite <- Hbeq in H5.
      assumption.
      apply Hc1eq.
      assumption.
    SCase "E_IfFalse".
      apply E_IfFalse.
      rewrite <- Hbeq in H5.
      assumption.
      apply Hc2eq.
      assumption.
Qed.

Example congruence_example:
  cequiv
    (X ::= ANum 0;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= ANum 0
     ELSE
       Y ::= ANum 42
     FI)
    (X ::= ANum 0;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= AMinus (AId X) (AId X)
     ELSE
       Y ::= ANum 42
     FI).
Proof.
  apply CSeq_congruence.
    apply refl_cequiv.
    apply CIf_congruence.
      apply refl_bequiv.
      apply CAss_congruence. unfold aequiv. simpl. lia.
      apply refl_cequiv.
Qed.

(********************************
  ケーススタディ: 定数畳み込み
*********************************)

(* -----
  プログラム変換の健全性
-------- *)
Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

(* -----
  定数畳み込み変換
-------- *)

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i => AId i
  | APlus a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => ANum (n1 + n2)
      | (a1', a2') => APlus a1' a2'
      end
  | AMinus a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => ANum (n1 - n2)
      | (a1', a2') => AMinus a1' a2'
      end
  | AMult a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => ANum (n1 * n2)
      | (a1', a2') => AMult a1' a2'
      end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp
      (AMult (APlus (ANum 1) (ANum 2)) (AId X))
  = AMult (ANum 3) (AId X).
Proof. reflexivity. Qed.

Example fold_aexp_ex2 :
    fold_constants_aexp
      (AMinus (AId X) (APlus (AMult (ANum 0) (ANum 6)) (AId Y)))
  = AMinus (AId X) (APlus (ANum 0) (AId Y)).
Proof. reflexivity. Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => if Nat.eqb n1 n2 then BTrue else BFalse
      | (a1', a2') => BEq a1' a2'
      end
  | BLe a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => if Nat.leb n1 n2 then BTrue else BFalse
      | (a1', a2') => BLe a1' a2'
      end
  | BNot b1 =>
      match (fold_constants_bexp b1) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2 =>
      match (fold_constants_bexp b1, fold_constants_bexp b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.

Example fold_bexp_ex1 :
    fold_constants_bexp (BAnd BTrue (BNot (BAnd BFalse BTrue)))
  = BTrue.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
    fold_constants_bexp
      (BAnd (BEq (AId X) (AId Y))
            (BEq (ANum 0)
                 (AMinus (ANum 2) (APlus (ANum 1) (ANum 1)))))
  = BAnd (BEq (AId X) (AId Y)) BTrue.
Proof. reflexivity. Qed.

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP =>
      SKIP
  | i ::= a =>
      CAss i (fold_constants_aexp a)
  | c1 ; c2 =>
      (fold_constants_com c1) ; (fold_constants_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
      | BTrue => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => IFB b' THEN fold_constants_com c1
                     ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END =>
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.

Example fold_com_ex1 :
  fold_constants_com
    (X ::= APlus (ANum 4) (ANum 5);
     Y ::= AMinus (AId X) (ANum 3);
     IFB BEq (AMinus (AId X) (AId Y)) (APlus (ANum 2) (ANum 4)) THEN
       SKIP
     ELSE
       Y ::= ANum 0
     FI;
     IFB BLe (ANum 0) (AMinus (ANum 4) (APlus (ANum 2) (ANum 1))) THEN
       Y ::= ANum 0
     ELSE
       SKIP
     FI;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END) =
  (X ::= ANum 9;
   Y ::= AMinus (AId X) (ANum 3);
   IFB BEq (AMinus (AId X) (AId Y)) (ANum 6) THEN
     SKIP
   ELSE
     (Y ::= ANum 0)
   FI;
   Y ::= ANum 0;
   WHILE BEq (AId Y) (ANum 0) DO
     X ::= APlus (AId X) (ANum 1)
   END).
Proof. reflexivity. Qed.

(* -----
  定数畳み込みの健全性
-------- *)
Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  aexp_cases (induction a) Case; simpl;
    
    try reflexivity;
    
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity).
Qed.

(* 練習問題: ★★★, optional (fold_bexp_BEq_informal) *)
Theorem fold_constants_bexp_sound :
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  bexp_cases (induction b) Case;
    
    try reflexivity.
  Case "BEq".
    rename a into a1. rename a0 into a2. simpl.
    remember (fold_constants_aexp a1) as a1'.
    remember (fold_constants_aexp a2) as a2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
      simpl. destruct (Nat.eqb n n0); reflexivity.
  Case "BLe".
    rename a into a1.
    rename a0 into a2.
    simpl.
    remember (fold_constants_aexp a1) as a1'.
    remember (fold_constants_aexp a2) as a2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
      simpl. destruct (Nat.leb n n0); reflexivity.
  Case "BNot".
    simpl. remember (fold_constants_bexp b) as b'.
    rewrite IHb.
    destruct b'; reflexivity.
  Case "BAnd".
    simpl.
    remember (fold_constants_bexp b1) as b1'.
    remember (fold_constants_bexp b2) as b2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
Admitted.

(* 練習問題: ★★★ (fold_constants_com_sound) *)
Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  com_cases (induction c) Case; simpl.
  Case "SKIP". apply refl_cequiv.
  Case "::=". apply CAss_congruence. apply fold_constants_aexp_sound.
  Case ";". apply CSeq_congruence; assumption.
  Case "IFB".
    assert (bequiv b (fold_constants_bexp b)).
      SCase "Pf of assertion". apply fold_constants_bexp_sound.
    remember (fold_constants_bexp b) as b'.
    destruct b';
      try (apply CIf_congruence; assumption).
    SCase "b always true".
      apply trans_cequiv with c1; try assumption.
      apply IFB_true; assumption.
    SCase "b always false".
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  Case "WHILE".
    assert (bequiv b (fold_constants_bexp b)).
      SCase "Pf of assertion". apply fold_constants_bexp_sound.
    remember (fold_constants_bexp b) as b'.
    destruct b';
      try solve [
        apply CWhile_congruence; assumption
      ].
    SCase "b always true".
      apply WHILE_true.
      assumption.
    SCase "b always false".
      apply WHILE_false.
      assumption.
Qed.

(* -----
  (0 + n)の消去の健全性、再び
-------- *)

(* 練習問題: ★★★★, optional (optimize_0plus) *)
Fixpoint optimize_0plus_aexp (e : aexp) : aexp :=
  match e with
  | ANum n =>
      ANum n
  | AId i =>
      AId i
  | APlus (ANum 0) e2 =>
      optimize_0plus_aexp e2
  | APlus e1 e2 =>
      APlus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  end.

Fixpoint optimize_0plus_bexp (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>
      BEq (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | BLe a1 a2 =>
      BLe (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | BNot b1 =>
      BNot (optimize_0plus_bexp b1)
  | BAnd b1 b2 =>
      BAnd (optimize_0plus_bexp b1) (optimize_0plus_bexp b2)
  end.

Fixpoint optimize_0plus_com (c : com) : com :=
  match c with
  | SKIP =>
      SKIP
  | i ::= a =>
      CAss i (optimize_0plus_aexp a)
  | c1 ; c2 =>
      (optimize_0plus_com c1) ; (optimize_0plus_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      IFB (optimize_0plus_bexp b) THEN (optimize_0plus_com c1) ELSE (optimize_0plus_com c2) FI
  | WHILE b DO c END =>
      WHILE (optimize_0plus_bexp b) DO (optimize_0plus_com c) END
  end.

Theorem optimize_0plus_aexp_sound :
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound, aequiv.
  intros.
  aexp_cases (induction a) Case; simpl;
    try solve [
      reflexivity
    ];
    try solve [
      rewrite IHa1;
      rewrite IHa2;
      reflexivity
    ].
  Case "APlus".
    aexp_cases (induction a1) SCase;
      try solve [
        rewrite IHa1;
        rewrite IHa2;
        reflexivity
      ].
      destruct n;
        try solve [
          rewrite IHa1;
          rewrite IHa2;
          reflexivity
        ].
Qed.

Theorem optimize_0plus_bexp_sound :
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound, bequiv.
  intros.
  bexp_cases (induction b) Case;
    try solve [
      reflexivity
    ];
    try solve [
      simpl;
      rewrite (optimize_0plus_aexp_sound a);
      rewrite (optimize_0plus_aexp_sound a0);
      reflexivity
    ].
  Case "BNot".
    simpl.
    rewrite IHb.
    reflexivity.
  Case "BAnd".
    simpl.
    rewrite IHb1.
    rewrite IHb2.
    reflexivity.
Qed.

Theorem optimize_0plus_com_sound :
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound.
  intros.
  com_cases (induction c) Case; simpl.
  Case "SKIP".
    apply refl_cequiv.
  Case "::=".
    apply CAss_congruence.
    apply optimize_0plus_aexp_sound.
  Case ";".
    apply CSeq_congruence.
    assumption.
    assumption.
  Case "IFB".
    apply CIf_congruence.
    apply optimize_0plus_bexp_sound.
    assumption.
    assumption.
  Case "WHILE".
    apply CWhile_congruence.
    apply optimize_0plus_bexp_sound.
    assumption.
Qed.

Definition optimize_fold_const_0plus (c : com) : com :=
  optimize_0plus_com (fold_constants_com c).

Example optimize_fold_const_0plus_ex1 :
  optimize_fold_const_0plus
    (
      X ::= APlus (ANum 4) (ANum 5);
      Y ::= APlus (ANum 0) (AId X)
    )
  =
    (
      X ::= ANum 9;
      Y ::= AId X
    ).
Proof. reflexivity. Qed.

Theorem optimize_fold_const_0plus_sound :
  ctrans_sound optimize_fold_const_0plus.
Proof.
  unfold ctrans_sound.
  intros.
  unfold optimize_fold_const_0plus.
  apply trans_cequiv with (c2 := (fold_constants_com c)).
  apply fold_constants_com_sound.
  apply optimize_0plus_com_sound.
Qed.

(********************************
  プログラムが同値でないことを証明する
*********************************)
Fixpoint subst_aexp (i : Id.id) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i' => if Id.beq_id i i' then u else AId i'
  | APlus a1 a2 => APlus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMinus a1 a2 => AMinus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMult a1 a2 => AMult (subst_aexp i u a1) (subst_aexp i u a2)
  end.

Example subst_aexp_ex :
  subst_aexp X (APlus (ANum 42) (ANum 53)) (APlus (AId Y) (AId X)) =
  (APlus (AId Y) (APlus (ANum 42) (ANum 53))).
Proof. reflexivity. Qed.

Definition subst_equiv_property := forall i1 i2 a1 a2,
  cequiv (i1 ::= a1; i2 ::= a2)
         (i1 ::= a1; i2 ::= subst_aexp i1 a1 a2).

Theorem subst_inequiv :
   ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.

  remember (X ::= APlus (AId X) (ANum 1);
            Y ::= AId X)
      as c1.
  remember (X ::= APlus (AId X) (ANum 1);
            Y ::= APlus (AId X) (ANum 1))
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).

  remember (update (update empty_state X 1) Y 1) as st1.
  remember (update (update empty_state X 1) Y 2) as st2.
  assert (H1: c1 / empty_state || st1);
  assert (H2: c2 / empty_state || st2);
  try (subst;
       apply E_Seq with (st' := (update empty_state X 1));
       apply E_Ass; reflexivity).
  apply H in H1.

  assert (Hcontra: st1 = st2)
    by (apply (ceval_deterministic c2 empty_state); assumption).
  assert (Hcontra': st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst.
  inversion Hcontra'.
Qed.

(* 練習問題: ★★★★ (better_subst_equiv) *)
Inductive var_not_used_in_aexp (X : Id.id) : aexp -> Prop :=
  | VNUNum: forall n, var_not_used_in_aexp X (ANum n)
  | VNUId: forall Y, X <> Y -> var_not_used_in_aexp X (AId Y)
  | VNUPlus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (APlus a1 a2)
  | VNUMinus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMinus a1 a2)
  | VNUMult: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMult a1 a2).

Lemma aeval_weakening :
  forall i st a ni,
  var_not_used_in_aexp i a ->
  aeval (update st i ni) a = aeval st a.
Proof.
  intros i st a ni Hvar_not_in.
  aexp_cases (induction a) Case; simpl;
    try solve [
      reflexivity
    ];
    try solve [
      inversion Hvar_not_in; subst;
      try rewrite IHa1;
      try rewrite IHa2;
      try reflexivity;
      assumption;
      assumption
    ].
  Case "AId".
    rename i0 into i'.
    unfold update.
    inversion Hvar_not_in; subst.
    rewrite Id.not_eq_beq_id_false.
    reflexivity.
    assumption.
Qed.

Definition subst_equiv_property' :=
  forall i1 i2 a1 a2,
  var_not_used_in_aexp i1 a1 ->
  cequiv (i1 ::= a1; i2 ::= a2)
         (i1 ::= a1; i2 ::= subst_aexp i1 a1 a2).

Theorem subst_equiv :
   subst_equiv_property'.
Proof.
  unfold subst_equiv_property', cequiv.
  intros i1 i2 a1 a2 Hvar_not_in st st''.
  split; intros.
  Case "->".
    apply E_Seq with (st' := update st i1 (aeval st a1)).

    inversion H; subst.
    inversion H2; subst.
    assumption.

    inversion H; subst.
    inversion H2; subst.
    inversion H5; subst.
    apply E_Ass.
    remember (update st i1 (aeval st a1)) as st'.
    aexp_cases (induction a2) SCase; simpl;
      try solve [
        reflexivity
      ];
      try solve [
        rewrite IHa2_1;
        try rewrite IHa2_2;
        try reflexivity;
        eauto using ceval
      ].
    SCase "AId".
      remember (Id.beq_id i1 i) as ii.
      destruct (ii).
      SSCase "i1 = i".
        apply Id.beq_id_eq in Heqii.
        subst i.
        subst st'.
        rewrite update_eq.
        specialize (aeval_weakening _ st _ (aeval st a1) Hvar_not_in) as weaking.
        rewrite weaking.
        reflexivity.
      SSCase "i1 <> i".
        simpl.
        reflexivity.
  Case "<-".
    apply E_Seq with (st' := update st i1 (aeval st a1)).

    inversion H; subst.
    inversion H2; subst.
    assumption.

    inversion H; subst.
    inversion H2; subst.
    inversion H5; subst.
    apply E_Ass.
    remember (update st i1 (aeval st a1)) as st'.
    aexp_cases (induction a2) SCase; simpl;
      try solve [
        reflexivity
      ];
      try solve [
        rewrite IHa2_1;
        try rewrite IHa2_2;
        try reflexivity;
        eauto using ceval
      ].
    SCase "AId".
      remember (Id.beq_id i1 i) as ii.
      destruct (ii).
      SSCase "i1 = i".
        apply Id.beq_id_eq in Heqii.
        subst i.
        subst st'.
        rewrite update_eq.
        specialize (aeval_weakening _ st _ (aeval st a1) Hvar_not_in) as weaking.
        rewrite weaking.
        reflexivity.
      SSCase "i1 <> i".
        simpl.
        reflexivity.
Qed.

(* 練習問題: ★★★, recommended (inequiv_exercise) *)
Theorem inequiv_exercise:
  ~ cequiv (WHILE BTrue DO SKIP END) SKIP.
Proof.
  unfold not, cequiv.
  intros contra.
  assert (SKIP / empty_state || empty_state).
    constructor.
  apply (contra empty_state empty_state) in H.
  apply (loop_never_stops empty_state empty_state) in H.
  assumption.
Qed.

(********************************
  外延性を使わずに行う (Optional)
*********************************)
Definition stequiv (st1 st2 : state) : Prop :=
  forall (X : Id.id), st1 X = st2 X.
Notation "st1 '~' st2" := (stequiv st1 st2) (at level 30).

(* 練習問題: ★, optional (stequiv_refl) *)
Lemma stequiv_refl :
  forall (st : state),
  st ~ st.
Proof.
  unfold stequiv.
  intros.
  reflexivity.
Qed.

(* 練習問題: ★, optional (stequiv_sym) *)
Lemma stequiv_sym :
  forall (st1 st2 : state),
  st1 ~ st2 ->
  st2 ~ st1.
Proof.
  unfold stequiv.
  intros.
  symmetry.
  apply H.
Qed.

(* 練習問題: ★, optional (stequiv_trans) *)
Lemma stequiv_trans :
  forall (st1 st2 st3 : state),
  st1 ~ st2 ->
  st2 ~ st3 ->
  st1 ~ st3.
Proof.
  unfold stequiv.
  intros st1 st2 st3 Hst12 Hst23 X.
  rewrite Hst12.
  apply Hst23.
Qed.

(* 練習問題: ★, optional (stequiv_update) *)
Lemma stequiv_update :
  forall (st1 st2 : state),
  st1 ~ st2 ->
  forall (X : Id.id) (n : nat),
  update st1 X n ~ update st2 X n.
Proof.
  unfold stequiv.
  intros st1 st2 Hsteq X n Y.
  unfold update.
  destruct (Id.beq_id X Y).
  Case "X = Y".
    reflexivity.
  Case "X <> Y".
    apply Hsteq.
Qed.

(* 練習問題: ★★, optional (stequiv_aeval) *)
Lemma stequiv_aeval :
  forall (st1 st2 : state),
  st1 ~ st2 ->
  forall (a : aexp), aeval st1 a = aeval st2 a.
Proof.
  unfold stequiv.
  intros st1 st2 Hsteq a.
  aexp_cases (induction a) Case; simpl;
    try solve [
      try rewrite IHa1;
      try rewrite IHa2;
      reflexivity
    ].
  Case "AId".
    apply Hsteq.
Qed.

(* 練習問題: ★★, optional (stequiv_beval) *)
Lemma stequiv_beval :
  forall (st1 st2 : state),
  st1 ~ st2 ->
  forall (b : bexp), beval st1 b = beval st2 b.
Proof.
  unfold stequiv.
  intros st1 st2 Hsteq b.
  bexp_cases (induction b) Case; simpl;
    try solve [
      try rewrite IHb;
      try rewrite IHb1;
      try rewrite IHb2;
      reflexivity
    ];
    try solve [
      repeat rewrite (stequiv_aeval st1 st2);
      try reflexivity;
      assumption
    ].
Qed.

Lemma stequiv_ceval: forall (st1 st2 : state),
  st1 ~ st2 ->
  forall (c: com) (st1': state),
    (c / st1 || st1') ->
    exists st2' : state,
      ((c / st2 || st2') /\ st1' ~ st2').
Proof.
  intros st1 st2 STEQV c st1' CEV1. generalize dependent st2.
  induction CEV1; intros st2 STEQV.
  Case "SKIP".
    exists st2. split.
      constructor.
      assumption.
  Case ":=".
    exists (update st2 l n). split.
       constructor. rewrite <- H. symmetry. apply stequiv_aeval.
       assumption. apply stequiv_update. assumption.
  Case ";".
    destruct (IHCEV1_1 st2 STEQV) as [st2' [P1 EQV1]].
    destruct (IHCEV1_2 st2' EQV1) as [st2'' [P2 EQV2]].
    exists st2''. split.
      apply E_Seq with st2'; assumption.
      assumption.
  Case "IfTrue".
    destruct (IHCEV1 st2 STEQV) as [st2' [P EQV]].
    exists st2'. split.
      apply E_IfTrue. rewrite <- H. symmetry. apply stequiv_beval.
      assumption. assumption. assumption.
  Case "IfFalse".
    destruct (IHCEV1 st2 STEQV) as [st2' [P EQV]].
    exists st2'. split.
     apply E_IfFalse. rewrite <- H. symmetry. apply stequiv_beval.
     assumption. assumption. assumption.
  Case "WhileEnd".
    exists st2. split.
      apply E_WhileEnd. rewrite <- H. symmetry. apply stequiv_beval.
      assumption. assumption.
  Case "WhileLoop".
    destruct (IHCEV1_1 st2 STEQV) as [st2' [P1 EQV1]].
    destruct (IHCEV1_2 st2' EQV1) as [st2'' [P2 EQV2]].
    exists st2''. split.
      apply E_WhileLoop with st2'. rewrite <- H. symmetry.
      apply stequiv_beval. assumption. assumption. assumption.
      assumption.
Qed.

Reserved Notation "c1 '/' st '||'' st'" (at level 40, st at level 39).
Inductive ceval' : com -> state -> state -> Prop :=
  | E_equiv : forall c st st' st'',
    c / st || st' ->
    st' ~ st'' ->
    c / st ||' st''
  where "c1 '/' st '||'' st'" := (ceval' c1 st st').

Definition cequiv' (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st ||' st') <-> (c2 / st ||' st').

Lemma cequiv__cequiv' :
  forall (c1 c2: com),
  cequiv c1 c2 -> cequiv' c1 c2.
Proof.
  unfold cequiv, cequiv'; split; intros.
    inversion H0 ; subst. apply E_equiv with st'0.
    apply (H st st'0); assumption. assumption.
    inversion H0 ; subst. apply E_equiv with st'0.
    apply (H st st'0). assumption. assumption.
Qed.

(* 練習問題: ★★, optional (identity_assignment') *)
Example identity_assignment' :
  cequiv' SKIP (X ::= AId X).
Proof.
    unfold cequiv'.
    intros.
    split; intros.
    Case "->".
      inversion H; subst; clear H.
      inversion H0; subst.
      rename st'0 into st.
      apply E_equiv with (update st X (st X)).
      constructor.
      reflexivity.
      apply stequiv_trans with st.
      unfold stequiv.
      intros.
      apply update_same.
      reflexivity.
      assumption.
    Case "<-".
      apply E_equiv with (st' := st).
      constructor.      
      inversion H; subst; clear H.
      inversion H0; subst.
      simpl in H1.
      apply stequiv_trans with (st2 := update st X (st X)).
      unfold stequiv.
      intros.
      symmetry.
      apply update_same.
      reflexivity.
      assumption.
Qed.

(********************************
  さらなる練習問題
*********************************)
(* todo *)
