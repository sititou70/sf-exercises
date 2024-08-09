Require Import Unicode.Utf8.
Require Import commons.
Require Import Prop_J.
Require Import List.

(********************************
  全称量化と含意
*********************************)
Definition funny_prop1 := ∀ n, ∀ (E : ev n), ev (n + 4).

Definition funny_prop1' := ∀ n, ∀ (_ : ev n), ev (n+4).

Definition funny_prop1'' := ∀ n, ev n → ev (n+4).

(********************************
  論理積、連言（Conjunction、AND）
*********************************)

Inductive and (P Q : Prop) : Prop :=
  conj : P → Q → (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

Check conj.

Theorem and_example :
  (ev 0) /\ (ev 4).
Proof.
  apply conj.
  apply ev_0.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Print and_example.

Theorem and_example' :
  (ev 0) /\ (ev 4).
Proof.
  split.
    Case "left". apply ev_0.
    Case "right". apply ev_SS. apply ev_SS. apply ev_0.
Qed.

Theorem proj1 :
  ∀ P Q : Prop,
  P /\ Q →
  P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HP.
Qed.

(* 練習問題: ★, optional (proj2) *)
Theorem proj2 :
  ∀ P Q : Prop,
  P /\ Q →
  Q.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HQ.
Qed.

Theorem and_commut :
  ∀ P Q : Prop,
  P ∧ Q →
  Q ∧ P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  split.
  apply HQ.
  apply HP.
Qed.

Print and_commut.

(* 練習問題: ★★ (and_assoc) *)
Theorem and_assoc :
  ∀ P Q R : Prop,
  P ∧ (Q ∧ R) →
  (P ∧ Q) ∧ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split.
  split.
  apply HP.
  apply HQ.
  apply HR.
Qed.

(* 練習問題: ★★, recommended (even_ev) *)
Theorem even_ev :
  ∀ n : nat,
  (even n → ev n) /\ (even (S n) → ev (S n)).
Proof.
  intros.
  induction n as [| n'].
  Case "n = 0".
    split.
    SCase "left".
      intros.
      apply ev_0.
    SCase "right".
      intros.
      inversion H.
  Case "n = S n'".
    split.
    SCase "left".
      intros.
      inversion IHn'.
      apply H1 in H.
      apply H.
    SCase "right".
      intros.
      inversion IHn'.
      assert (even_ssx__even_x: ∀ x : nat, even (S (S x)) -> even x).
        SSCase "Proof of assertion".
          intros.
          unfold even.
          inversion H2.
          reflexivity.
      apply even_ssx__even_x in H.
      apply H0 in H.
      apply ev_SS.
      apply H.
Qed.

(* 練習問題: ★★ *)
Definition conj_fact :
  ∀ P Q R,
  P /\ Q →
  Q /\ R →
  P /\ R :=
    fun (P Q R : Prop) (HPQ : P /\ Q) (HQR : Q /\ R) =>
      let p :=
        match HPQ with
        | conj _ _ p _ => p
        end
      in
      let r :=
        match HQR with
        | conj _ _ _ r => r
        end
      in
      conj P R p r.

(* -----
  Iff （両含意）
-------- *)

Definition iff (P Q : Prop) := (P → Q) /\ (Q → P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity) : type_scope.

Theorem iff_implies :
  ∀ P Q : Prop,
  (P ↔ Q) →
  P → Q.
Proof.
  intros P Q H.
  inversion H as [HAB HBA]. apply HAB.
Qed.

Theorem iff_sym :
  ∀ P Q : Prop,
  (P ↔ Q) →
  (Q ↔ P).
Proof.
  intros P Q H.
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB.
Qed.

(* 練習問題: ★ (iff_properties) *)
Theorem iff_refl :
  ∀ P : Prop,
  P ↔ P.
Proof.
  intros.
  split.
  intros.
  apply H.
  intros.
  apply H.
Qed.

Theorem iff_trans :
  ∀ P Q R : Prop,
  (P ↔ Q) →
  (Q ↔ R) →
  (P ↔ R).
Proof.
  intros P Q R HPQ HQR.
  split.
  Case "P -> R".
    intros.
    apply HQR.
    apply HPQ.
    apply H.
  Case "R -> P".
    intros.
    apply HPQ.
    apply HQR.
    apply H.
Qed.

(* 練習問題: ★★ (MyProp_iff_ev) *)
Definition MyProp_iff_ev : ∀ n, MyProp n <-> ev n :=
  fun (n : nat) =>
    conj (MyProp n -> ev n) (ev n -> MyProp n) (ev_MyProp n) (MyProp_ev n).

(********************************
  論理和、選言（Disjunction、OR）
*********************************)
Inductive or (P Q : Prop) : Prop :=
  | or_introl : P → or P Q
  | or_intror : Q → or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Check or_introl.

Check or_intror.

Theorem or_commut :
  ∀ P Q : Prop,
  P \/ Q →
  Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "right". apply or_intror. apply HP.
    Case "left". apply or_introl. apply HQ.
Qed.

Theorem or_commut' :
  ∀ P Q : Prop,
  P \/ Q →
  Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "right". right. apply HP.
    Case "left". left. apply HQ.
Qed.

(* 練習問題: ★★ optional (or_commut'') *)
Definition or_commut'' : ∀ P Q : Prop, P \/ Q -> Q \/ P
  := fun (P Q : Prop) (H : P \/ Q) =>
    match H with
    | or_introl _ _ p => or_intror Q P p
    | or_intror _ _ q => or_introl Q P q
    end.

Theorem or_distributes_over_and_1 :
  ∀ P Q R : Prop,
  P \/ (Q /\ R) →
  (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. intros H. inversion H as [HP | [HQ HR]].
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR.
Qed.

(* 練習問題: ★★, recommended (or_distributes_over_and_2) *)
Theorem or_distributes_over_and_2 :
  ∀ P Q R : Prop,
  (P \/ Q) /\ (P \/ R) →
  P \/ (Q /\ R).
Proof.
  intros.
  inversion H as [PQ PR].
  destruct PQ as [PQ_P | PQ_Q].
  Case "PQ_P".
    left.
    apply PQ_P.
  Case "PQ_Q".
    destruct PR as [PR_P | PR_R].
    SCase "PR_P".
      left.
      apply PR_P.
    SCase "PR_R".
      right.
      split.
        SSCase "Q".
          apply PQ_Q.
        SSCase "R".
          apply PR_R.
Qed.

(* 練習問題: ★ (or_distributes_over_and) *)
Theorem or_distributes_over_and :
  ∀ P Q R : Prop,
  P \/ (Q /\ R) ↔ (P \/ Q) /\ (P \/ R).
Proof.
  intros.
  split.
  apply or_distributes_over_and_1.
  apply or_distributes_over_and_2.
Qed.

(* -----
  ∧ 、 ∨ のandb 、orb への関連付け
-------- *)
Theorem andb_true__and :
  ∀ b c,
  andb b c = true →
  b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H.
Qed.

Theorem and__andb_true :
  ∀ b c,
  b = true /\ c = true →
  andb b c = true.
Proof.
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity.
Qed.

(* 練習問題: ★ (bool_prop) *)
Theorem andb_false :
  ∀ b c,
  andb b c = false →
  b = false \/ c = false.
Proof.
  intros.
  destruct H.
  destruct b.
  Case "b = true".
    right.
    reflexivity.
  Case "b = false".
    left.
    reflexivity.
Qed.

Theorem orb_true :
  ∀ b c,
  orb b c = true →
  b = true \/ c = true.
Proof.
  intros.
  destruct H.
  destruct b.
  Case "b = true".
    left.
    reflexivity.
  Case "b = false".
    right.
    reflexivity.
Qed.

Theorem orb_false :
  ∀ b c,
  orb b c = false →
  b = false /\ c = false.
Proof.
  intros.
  destruct b.
  Case "b = true".
    inversion H.
  Case "b = false".
    split.
    reflexivity.
    apply H.
Qed.

(********************************
  偽であるということ
*********************************)
Inductive False : Prop := .

(* 練習問題: ★ (False_ind_principle) *)
(* Falseの帰納法の原理がある。 *)
Print False_ind.
(* Falseの根拠があればあらゆる命題を主張できることを意味する。 *)

Theorem False_implies_nonsense :
  False → 2 + 2 = 5.
Proof.
  intros contra.
  inversion contra.
Qed.

Theorem nonsense_implies_False :
  2 + 2 = 5 → False.
Proof.
  intros contra.
  inversion contra.
Qed.

Theorem ex_falso_quodlibet :
  ∀ (P:Prop),
  False → P.
Proof.
  intros P contra.
  inversion contra.
Qed.

(* -----
  真であるということ
-------- *)

(* 練習問題: ★★ (True_induction) *)
Inductive MyTrue : Prop :=
  | MyTrueCons : MyTrue.
Check MyTrue_ind.
Check True_ind.

(********************************
  否定
*********************************)
Definition not (P : Prop) := P → False.

Notation "~ x" := (not x) : type_scope.

Check not.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. inversion H.
Qed.

Theorem contradiction_implies_anything :
  ∀ P Q : Prop,
  (P /\ ~P) →
  Q.
Proof.
  intros P Q H. inversion H as [HP HNA]. unfold not in HNA.
  apply HNA in HP. inversion HP.
Qed.

Theorem double_neg : ∀ P : Prop,
  P → ~~P.
Proof.
  intros P H. unfold not. intros G. apply G. apply H. Qed.

(* 練習問題: ★★, recommended (double_neg_inf) *)

(*
定理：すべての命題Pについて、Pならば~~Pである。

証明：

Pを仮定して~~Pを示す。

notを展開すると~P -> False、さらに展開すると(P -> False) -> Falseとなる。

(P -> False)を仮定してFalseを示す。

仮定よりPであり(P -> False)なので、Falseが示せた。

したがって所望の結論が成り立つ。
*)

(* 練習問題: ★★, recommended (contrapositive) *)
Theorem contrapositive :
  ∀ P Q : Prop,
  (P → Q) →
  (~Q → ~P).
Proof.
  intros.
  unfold not.
  intros.
  unfold not in H0.
  apply H in H1.
  apply H0 in H1.
  inversion H1.
Qed.

(* 練習問題: ★ (not_both_true_and_false) *)
Theorem not_both_true_and_false :
  ∀ P : Prop,
  ~ (P /\ ~P).
Proof.
  intros.
  unfold not.
  intros.
  inversion H.
  apply H1 in H0.
  inversion H0.
Qed.

Theorem five_not_even :
  ~ ev 5.
Proof.
  unfold not. intros Hev5. inversion Hev5 as [|n Hev3 Heqn].
  inversion Hev3 as [|n' Hev1 Heqn']. inversion Hev1.
Qed.

(* 練習問題: ★ ev_not_ev_S *)
Theorem ev_not_ev_S :
  ∀ n,
  ev n →
  ~ ev (S n).
Proof.
  unfold not.
  intros n H.
  induction H.
  Case "ev (S 0)".
    intros.
    inversion H.
  Case "ev (S (S (S n)))".
    intros HSSSn.
    inversion HSSSn as [| n' HSn Hn'].
    apply IHev in HSn.
    inversion HSn.
Qed.

(* 練習問題: ★ (informal_not_PNP) *)
(*
定理：すべての命題Pについて、~(P /\ ~P)

証明：

notを展開すると、(P /\ ~P) -> False。更に展開すると(P /\ (P -> False)) -> False

(P /\ (P -> False))を仮定してFalseを示す。仮定より、Pかつ(P -> False)であるため、Falseが示された。
*)

Theorem classic_double_neg :
  ∀ P : Prop,
  ~~P → P.
Proof.
  intros P H. unfold not in H.
  Admitted.

(* 練習問題: ★★★★★, optional (classical_axioms) *)
Definition peirce := ∀ P Q : Prop,
  ((P -> Q) -> P) -> P.
Definition classic := ∀ P : Prop,
  ~~P -> P.
Definition excluded_middle := ∀ P : Prop,
  P \/ ~P.
Definition de_morgan_not_and_not := ∀ P Q : Prop,
  ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := ∀ P Q : Prop,
  (P -> Q) -> (~P \/ Q).

Theorem classic_eq_peirce :
  classic <-> peirce.
Proof.
  unfold classic.
  unfold peirce.
  unfold not.
  split.
  Case "->".
    intros.
    apply H.
    intros.
    apply H1.
    apply H0.
    intros.
    apply H1 in H2.
    inversion H2.
  Case "<-".
    intros.
    assert (PFP: (P -> False) -> P).
      SCase "Proof of assertion".
      intros.
      apply H0 in H1.
      inversion H1.
    apply H in PFP.
    apply PFP.
Qed.

Theorem classic_eq_excluded_middle :
  classic <-> excluded_middle.
Proof.
  unfold classic.
  unfold excluded_middle.
  unfold not.
  split.
  Case "->".
    (* https://x.com/sititou70/status/1751235004267643362/photo/1 *)
    intros.
    apply H.
    intros.
    apply H0.
    right.
    intros.
    apply H0.
    left.
    apply H1.
  Case "<-".
    intros.
    assert (PnPP: (P \/ ~P) -> P).
    SCase "Proof of assertion".
      intros.
      inversion H1.
      SSCase "P".
        apply H2.
      SSCase "~P".
        unfold not in H2.
        apply H0 in H2.
        inversion H2.
    apply PnPP in H.
    apply H.
Qed.

Theorem classic_eq_de_morgan_not_and_not :
  classic <-> de_morgan_not_and_not.
Proof.
  unfold classic.
  unfold de_morgan_not_and_not.
  unfold not.
  split.
  Case "->".
    intros.
    apply H.
    intros.
    apply H0.
    split.
    SCase "P -> False".
      intros.
      apply H1.
      left.
      apply H2.
    SCase "Q -> False".
      intros.
      apply H1.
      right.
      apply H2.
  Case "<-".
    intros.
    assert (PP: P \/ P).
    SCase "Proof of assertion".
      apply H.
      intros.
      apply H0.
      apply H1.
    destruct PP.
    SCase "P".
      apply H1.
    SCase "P".
      apply H1.  
Qed.

Theorem classic_eq_implies_to_or :
  classic <-> implies_to_or.
Proof.
  unfold classic.
  unfold implies_to_or.
  unfold not.
  split.
  Case "->".
    intros.
    apply H.
    intros.
    apply H1.
    left.
    intros.
    apply H1.
    right.
    apply H0 in H2.
    apply H2.
  Case "<-".
    intros.
    assert (excluded_middle: ~P \/ P).
    SCase "Proof of assertion".
      apply H.
      intros.
      apply H1.
    destruct excluded_middle.
    SCase "NP".
      unfold not in H1.
      apply H0 in H1.
      inversion H1.
    SCase "P".
      apply H1.
Qed.

(* -----
  不等であるということ
-------- *)

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true :
  ∀ b : bool,
  b <> false →
  b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
Qed.

(* 練習問題: ★★, recommended (not_eq_beq_false) *)
Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Theorem not_eq_beq_false :
  ∀ n n' : nat,
  n <> n' →
  beq_nat n n' = false.
Proof.
  intros n.
  induction n.
  Case "n: 0".
    intros.
    destruct n'.
    SCase "n': 0".
      simpl.
      apply ex_falso_quodlibet.
      unfold not in H.
      apply H.
      reflexivity.
    SCase "n': S n'".
      simpl.
      reflexivity.
  Case "n: S n".
    destruct n'.
    SCase "n': 0".
      intros.
      simpl.
      reflexivity.
    SCase "n': S n'".
      intros.
      simpl.
      apply IHn.
      unfold not.
      intros.
      unfold not in H.
      apply H.
      apply eq_S.
      apply H0.
Qed.

(* 練習問題: ★★, optional (beq_false_not_eq) *)
Theorem beq_false_not_eq :
  ∀ n m,
  false = beq_nat n m →
  n <> m.
Proof.
  intros n.
  induction n.
  Case "n: 0".
    intros.
    destruct m.
    SCase "m: 0".
      simpl in H.
      inversion H.
    SCase "m: S m".
      unfold not.
      intros.
      inversion H0.
  Case "n: S n".
    destruct m.
    SCase "m: 0".
      intros.
      unfold not.
      intros.
      inversion H0.
    SCase "m: S m".
      intros.
      assert (NEQINC: ∀ x y : nat, x <> y -> S x <> S y).
      SSCase "Proof of assertion".
        intros.
        unfold not.
        intros.
        apply H0.
        inversion H1.
        reflexivity.
      apply NEQINC.
      apply IHn.
      apply H.
Qed.

(********************************
  存在量化子
*********************************)

Inductive ex (X : Type) (P : X → Prop) : Prop :=
  ex_intro : ∀ (witness : X), P witness → ex X P.

Definition some_nat_is_even : Prop :=
  ex nat ev.

Definition snie : some_nat_is_even :=
  ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2).
  reflexivity. Qed.

(* Example exists_example_1' :
  ∃ n,
  n + (n * n) = 6.
Proof.
  ∃ 2.
  reflexivity. Qed. *)

Theorem exists_example_2 :
  ∀ n,
  (exists m, n = 4 + m) →
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm].
  apply ex_intro with (witness := 2 + m).
  apply Hm. Qed.

(* 練習問題: ★ (english_exists) *)
(* ある自然数nについて、その後者が偶数になるものが存在する *)
Definition p : ex nat (fun n => ev (S n)) :=
  ex_intro
    nat
    (fun (n : nat) => ev (S n))
    (S O)
    (ev_SS O ev_0).

(* 練習問題: ★ (dist_not_exists) *)
Theorem dist_not_exists :
  ∀ (X : Type) (P : X → Prop),
  (∀ x, P x) → ~(exists x, ~P x).
Proof.
  intros.
  unfold not.
  intros.
  inversion H0.
  apply H1.
  apply H.
Qed.

(* 練習問題: ★★★, optional (not_exists_dist) *)
Theorem not_exists_dist :
  excluded_middle →
  ∀ (X : Type) (P : X → Prop),
  ~(exists x, ~P x) → (∀ x, P x).
Proof.
  unfold excluded_middle.
  intros EXM X P H x.
  unfold not in H.
  assert (PXNPX: P x \/ ~P x).
  Case "Proof of assertion".
    apply EXM.
  destruct PXNPX.
  Case "P x".
    apply H0.
  Case "~P x".
    unfold not in H0.
    apply ex_falso_quodlibet.
    apply H.
    apply ex_intro with (witness := x).
    apply H0.
Qed.

(* 練習問題: ★★ (dist_exists_or) *)
Theorem dist_exists_or :
  ∀ (X : Type) (P Q : X → Prop),
  (exists x, P x \/ Q x) ↔ (exists x, P x) \/ (exists x, Q x).
Proof.
  split.
  Case "->".
    intros.
    inversion H as [x PXQX].
    destruct PXQX.
    SCase "P x".
      left.
      apply ex_intro with (witness := x).
      apply H0.
    SCase "Q x".
      right.
      apply ex_intro with (witness := x).
      apply H0.
  Case "<-".
    intros.
    destruct H.
    SCase "exists x : X, P x".
      inversion H as [x].
      apply ex_intro with (witness := x).
      left.
      apply H0.
    SCase "exists x : X, Q x".
      inversion H as [x].
      apply ex_intro with (witness := x).
      right.
      apply H0.
Qed.

(********************************
  等しいということ（同値性）
*********************************)
Module MyEquality.
  Inductive eq (X : Type) : X → X → Prop :=
    refl_equal : ∀ x, eq X x x.

  Notation "x = y" := (eq _ x y)
                      (at level 70, no associativity) : type_scope.

  Inductive eq' (X : Type) (x : X) : X → Prop :=
      refl_equal' : eq' X x x.

  Notation "x =' y" := (eq' _ x y)
                      (at level 70, no associativity) : type_scope.

  (* 練習問題: ★★★, optional (two_defs_of_eq_coincide) *)
  Theorem two_defs_of_eq_coincide :
    ∀ (X : Type) (x y : X),
    x = y ↔ x =' y.
  Proof.
    split.
    Case "->".
      intros.
      inversion H.
      apply refl_equal'.
    Case "<-".
      intros.
      inversion H.
      apply refl_equal.
  Qed.

  Check eq'_ind.

  Definition four : 2 + 2 = 1 + 3 :=
    refl_equal nat 4.
  Definition singleton : ∀ (X : Set) (x : X), [] ++ [x] = x :: [] :=
    fun (X : Set) (x : X) => refl_equal (list X) [x].
End MyEquality.

(********************************
  命題としての関係
*********************************)
Module LeFirstTry.
  Inductive le : nat → nat → Prop :=
    | le_n : ∀ n, le n n
    | le_S : ∀ n m, (le n m) → (le n (S m)).
End LeFirstTry.

Inductive le (n : nat) : nat → Prop :=
  | le_n : le n n
  | le_S : ∀ m, (le n m) → (le n (S m)).

Notation "m <= n" := (le m n).

Check le_ind.

Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n. Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 :
  ~ (2 <= 1).
Proof.
  intros H. inversion H. inversion H1. Qed.

Definition lt (n m : nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat → nat → Prop :=
  sq : ∀ n : nat, square_of n (n * n).

Inductive next_nat (n : nat) : nat → Prop :=
  | nn : next_nat n (S n).

Inductive next_even (n : nat) : nat → Prop :=
  | ne_1 : ev (S n) → next_even n (S n)
  | ne_2 : ev (S (S n)) → next_even n (S (S n)).

(* 練習問題: ★★, recommended (total_relation) *)
Inductive total_relation (n : nat) : nat → Prop :=
  | tr : ∀ m, total_relation n m.

(* 練習問題: ★★ (empty_relation) *)
Inductive empty_relation (n : nat) : nat → Prop := .

(* 練習問題: ★★★, recommended (R_provability) *)
Module R.
  Inductive R : nat → nat → nat → Prop :=
    | c1 : R 0 0 0
    | c2 : ∀ m n o, R m n o → R (S m) n (S o)
    | c3 : ∀ m n o, R m n o → R m (S n) (S o)
    | c4 : ∀ m n o, R (S m) (S n) (S (S o)) → R m n o
    | c5 : ∀ m n o, R m n o → R n m o.
  
  Example r112 : R 1 1 2.
  Proof.
    apply c2.
    apply c3.
    apply c1.
  Qed.

  Example r226 : R 2 2 6.
  Proof.
    Admitted.

  (*
    この関係からc4またはc5を取り除いても、証明可能な命題の範囲は変化しない。

    メモ：この関係のコンストラクタのうち、適用して数値を減少させるものはc2とc3のみである。
    ここで、関係の直接の証拠がc1しかないことを考慮すると、この関係が成り立つ命題とは、
    1、2番目の数値の合計が3番目の数値と等しいようなものである。
    c4、c5もまたこの規則にしたがっており、また数値を減少させないため、
    証明可能な命題の範囲を変化させることには寄与していない。
  *)

  (* 練習問題: ★★★, optional (R_fact) *)
  Theorem R_sum_eq : ∀ n1 n2 n3, R n1 n2 n3 -> n1 + n2 = n3.
  Proof.
    intros.
    induction H.
    Case "c1".
      reflexivity.
    Case "c2".
      rewrite <- IHR.
      apply PeanoNat.Nat.add_succ_l.
    Case "c3".
      rewrite <- IHR.
      apply PeanoNat.Nat.add_succ_r.
    Case "c4".
      simpl in IHR.
      apply PeanoNat.Nat.succ_inj in IHR.
      rewrite PeanoNat.Nat.add_succ_r in IHR.
      apply PeanoNat.Nat.succ_inj in IHR.
      apply IHR.
    Case "c5".
      rewrite PeanoNat.Nat.add_comm.
      apply IHR.
  Qed.
End R.

(* 練習問題: ★★★, recommended (all_forallb) *)
Inductive all {X : Type} (P : X → Prop) : list X → Prop :=
  | all_nil : all P nil
  | all_cons : ∀ (x : X) (l : list X), P x -> all P l -> all P (x :: l).

Fixpoint forallb {X : Type} (test : X → bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

Theorem forallb_eq_allb :
  ∀ (X : Type) (test : X -> bool) (l : list X),
  all (fun (x : X) => test x = true) l <-> forallb test l = true.
Proof.
  intros.
  split.
  Case "->".
    intros.
    induction H.
    SCase "l: []".
      reflexivity.
    SCase "l: x :: l".
      destruct l.
      SSCase "l: []".
        simpl.
        destruct (test x).
        SSSCase "test x = true".
          reflexivity.
        SSSCase "test x = false".
          inversion H.
      SSCase "l: x0 :: l".
        simpl.
        destruct (test x).
        SSSCase "test x = true".
          simpl.
          apply IHall.
        SSSCase "test x = false".
          inversion H.
  Case "<-".
    intros.
    induction l.
    SCase "l: []".
      apply all_nil.
    SCase "l: a :: l".
      assert (
        FAB_SPLIT:
          ∀ (X : Type) (x : X) (y : list X) (t : X -> bool),
          forallb t (x :: y) = true ->
          t x = true /\ forallb t y = true
      ).
      SSCase "Proof of assertion".
        intros.
        split.
        SSSCase "t x = true".
          inversion H0.
          destruct (t x).
            SSSSCase "t x = true".
            rewrite H2.
            reflexivity.
            SSSSCase "t x = false".
            simpl in H2.
            inversion H2.
        SSSCase "forallb t y = true".
          inversion H0.
          destruct (t x).
            SSSSCase "t x = true".
            reflexivity.
            SSSSCase "t x = false".
            simpl in H2.
            inversion H2.
      apply FAB_SPLIT in H.
      inversion H.
      apply IHl in H1.
      apply all_cons.
      SSCase "test a = true".
        apply H0.
      SSCase "all X (λ x : X, test x = true) l".
        apply H1.
Qed.

(* 練習問題: ★★★★, optional (filter_challenge) *)
Inductive merged_list {X : Type} : list X -> list X -> list X -> Prop :=
  | merged_nil : merged_list [] [] []
  | merged_cons1 : ∀ (x : X) (l1 l2 l : list X), merged_list l1 l2 l -> merged_list (x :: l1) l2 (x :: l)
  | merged_cons2 : ∀ (x : X) (l1 l2 l : list X), merged_list l1 l2 l -> merged_list l1 (x :: l2) (x :: l).

Fixpoint filter {X : Type} (test: X → bool) (l : list X) : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t) else filter test t
  end.

Theorem filter_challenge_1 :
  ∀ (X : Type) (l1 l2 l : list X) (test : X -> bool),
  merged_list l1 l2 l ->
  all (fun (x : X) => test x = true) l1 ->
  all (fun (x : X) => test x = false) l2 ->
  filter test l = l1.
Proof.
  intros.
  induction H.
  Case "merged_nil".
    reflexivity.
  Case "merged_cons1".
    inversion H0.
    apply IHmerged_list in H5.
    assert (
      filter_cons:
        ∀ (X : Type) (x : X) (l1 l : list X) (test : X -> bool),
        test x = true ->
        filter test l = l1 ->
        filter test (x :: l) = (x :: l1)
    ).
    SCase "Proof of assertion".
      intros.
      simpl.
      rewrite H6.
      rewrite H7.
      reflexivity.
    apply filter_cons.
    apply H4.
    apply H5.
    apply H1.    
  Case "merged_cons2".
    inversion H1.
    apply IHmerged_list in H5.
    assert (
      filter_cons:
        ∀ (X : Type) (x : X) (l1 l : list X) (test : X -> bool),
        test x = false ->
        filter test l = l1 ->
        filter test (x :: l) = l1
    ).
    SCase "Proof of assertion".
      intros.
      simpl.
      rewrite H6.
      apply H7.
    apply filter_cons.
    apply H4.
    apply H5.
    apply H0.
Qed.

(* 練習問題: ★★★★★, optional (filter_challenge_2) *)
(* https://ccvanishing.hateblo.jp/entry/2012/12/30/205251 *)
Inductive sublist {X : Type} : list X -> list X -> Prop :=
  | sublist_nil : forall (l : list X), sublist [] l
  | sublist_cons1 : forall (x : X) (l1 l : list X), sublist l1 l -> sublist (x :: l1) (x :: l)
  | sublist_cons2 : forall (x : X) (l1 l : list X), sublist l1 l -> sublist l1 (x :: l).

Fixpoint length {X:Type} (l:list X) : nat :=
  match l with
  | nil => 0
  | cons h t => S (length t)
  end.

Theorem filter_challenge_2 :
  forall (X : Type) (l subl : list X) (test : X -> bool),
  let TProp := (fun (x : X) => test x = true) in
  all TProp (filter test l) /\
  sublist (filter test l) l /\
  (
    all (fun (x : X) => test x = true) subl ->
    sublist subl l ->
    length subl <= length (filter test l)
  ).
Proof.
  intros.
  repeat split.
  Case "all TProp (filter test l)".
    induction l.
    SCase "l: []".
      simpl.
      apply all_nil.
    SCase "l: a :: l".
      simpl.
      case_eq (test a).
      SSCase "test a = true".
        intros.
        apply all_cons.
        apply H.
        apply IHl.
      SSCase "test a = false".
        intros.
        apply IHl.
  Case "sublist (filter test l) l".
    induction l.
    SCase "l: []".
      simpl.
      apply sublist_nil.
    SCase "l: a :: l".
      simpl.
      case_eq (test a).
      SSCase "test a = true".
        intros.
        apply sublist_cons1.
        apply IHl.
      SSCase "test a = false".
        intros.
        apply sublist_cons2.
        apply IHl;
  Case "length subl <= length (filter test l)".
    intros.
    assert (sublist_subl_filter: sublist subl (filter test l)).
    SCase "Proof of assertion".
      induction H0.
      SSCase "sublist_nil".
        apply sublist_nil.
      SSCase "sublist_cons1".
        simpl.
        case_eq (test x).
        SSSCase "test x = true".
          intros.
          apply sublist_cons1.
          inversion H.
          apply IHsublist in H5.
          apply H5.
        SSSCase "test x = false".
          intros.
          inversion H.
          rewrite H1 in H4.
          inversion H4.
      SSCase "sublist_cons2".
        apply IHsublist in H.
        simpl.
        case_eq (test x).
        SSSCase "test x = true".
          intros.
          apply sublist_cons2.
          apply H.
        SSSCase "test x = false".
          intros.
          apply H.
    assert (
      sublist_length_le:
        forall (l1 l2 : list X),
        sublist l1 l2 ->
        length l1 <= length l2
    ).
    SCase "Proof of assertion".
      intros.
      induction H1.
      SSCase "sublist_nil".
        simpl.
        destruct (length l0).
        SSSCase "length l0 = 0".
          apply le_n.
        SSSCase "length l0 = S n".
          induction n.
          SSSSCase "n = 0".
            apply le_S.
            apply le_n.
          SSSSCase "n = S n".
            apply le_S.
            apply IHn.
      SSCase "sublist_cons1".
        simpl.
        assert (
          n_le_sn:
            forall (n m : nat), n <= m -> S n <= S m
        ).
          intros.
          induction H2.
          SSSCase "le_n".
            apply le_n.
          SSSCase "le_S".
            apply le_S.
            apply IHle.
        apply n_le_sn.
        apply IHsublist.
      SSCase "sublist_cons2".
        simpl.
        apply le_S.
        apply IHsublist.
    apply sublist_length_le in sublist_subl_filter.
    apply sublist_subl_filter.
Qed.

(* 練習問題: ★★★★, optional (no_repeats) *)
Inductive appears_in {X : Type} (a : X) : list X → Prop :=
  | ai_here : ∀ l, appears_in a (a :: l)
  | ai_later : ∀ b l, appears_in a l → appears_in a (b :: l).

Lemma appears_in_app :
  ∀ {X : Type} (xs ys : list X) (x : X),
  appears_in x (xs ++ ys) ->
  appears_in x xs \/ appears_in x ys.
Proof.
  intros.
  induction xs.
  Case "xs: nil".
    right.
    apply H.
  Case "xs: a :: xs".
    inversion H.
    SCase "ai_here".
      left.
      apply ai_here.
    SCase "ai_later".
      apply IHxs in H1.
      destruct H1.
      SSCase "appears_in x xs".
        left.
        apply ai_later.
        apply H1.
      SSCase "appears_in x ys".
        right.
        apply H1.
Qed.

Lemma app_appears_in :
  ∀ {X : Type} (xs ys : list X) (x : X),
  appears_in x xs \/ appears_in x ys ->
  appears_in x (xs ++ ys).
Proof.
  intros.
  destruct H.
  Case "appears_in x xs".
    induction xs.
    SCase "xs: nil".
      inversion H.
    SCase "xs: a : xs".
      simpl.
      inversion H.
      SSCase "ai_here".
        apply ai_here.
      SSCase "ai_later".
        apply ai_later.
        apply IHxs in H1.
        apply H1.
  Case "appears_in x ys".
    induction xs.
    SCase "xs: nil".
      simpl.
      apply H.
    SCase "xs: a : xs".
      simpl.
      apply ai_later.
      apply IHxs.
Qed.

Inductive disjoint {X : Type} : list X -> list X -> Prop :=
  | disjoint_nil : disjoint [] []
  | disjoint_cons1 : ∀ (l1 l2 : list X) (x : X), ~ appears_in x l2 -> disjoint (x :: l1) l2
  | disjoint_cons2 : ∀ (l1 l2 : list X) (x : X), ~ appears_in x l1 -> disjoint l1 (x :: l2).

Example disjoint_eg1 : forall (X : Type), @disjoint X [] [].
Proof.
  intros.
  apply disjoint_nil.
Qed.
Example disjoint_eg2 : disjoint [0] [].
Proof.
  apply disjoint_cons1.
  unfold not.
  intros.
  inversion H.
Qed.
Example disjoint_eg3 : disjoint [] [0].
Proof.
  apply disjoint_cons2.
  unfold not.
  intros.
  inversion H.
Qed.
Example disjoint_eg4 : disjoint [0, 2] [1, 3].
Proof.
  apply disjoint_cons1.
  unfold not.
  intros.
  inversion H.
  inversion H1.
  inversion H4.
Qed.

Inductive no_repeats {X : Type} : list X -> Prop :=
  | no_repeats_nil : no_repeats []
  | no_repeats_cons : ∀ (l : list X) (x : X), ~ appears_in x l -> no_repeats (x :: l).

Example no_repeats_eg1 : no_repeats [1, 2, 3, 4].
Proof.
  apply no_repeats_cons.
  unfold not.
  intros.
  inversion H.
  inversion H1.
  inversion H4.
  inversion H7.
Qed.
Example no_repeats_eg2 : @no_repeats bool [].
Proof.
  apply no_repeats_nil.
Qed.

Theorem no_repeats_disjoin :
  forall (X : Type) (l1 l2 : list X),
  no_repeats (l1 ++ l2) ->
  disjoint l1 l2.
Proof.
  intros.
  destruct l1.
  Case "l1: []".
    simpl in H.
    inversion H.
    SSCase "no_repeats_nil".
      apply disjoint_nil.
    SSCase "no_repeats_cons".
      apply disjoint_cons2.
      unfold not.
      intros.
      inversion H2.
  Case "l1: a :: l1".
    simpl in H.
    apply disjoint_cons1.
    unfold not.
    intros.
    inversion H.
    SSCase "no_repeats_cons".
      unfold not in H2.
      apply or_intror with (P := appears_in x l1) in H0.
      apply app_appears_in in H0.
      apply H2 in H0.
      apply H0.
Qed.

(* -----
  少し脱線: <= と < についてのさらなる事実
-------- *)
(* 練習問題: ★★, optional (le_exercises) *)
Theorem O_le_n :
  ∀ n,
  0 <= n.
Proof.
  intros.
  induction n.
  Case "n = 0".
    apply le_n.
  Case "n = S n".
    apply le_S.
    apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm :
  ∀ n m,
  n <= m → S n <= S m.
Proof.
  intros.
  induction H.
  Case "le_n".
    apply le_n.
  Case "le_S".
    apply le_S.
    apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m :
  ∀ n m,
  S n <= S m → n <= m.
Proof.
  intros n m.
  generalize dependent n.
  induction m.
  Case "m = 0".
    intros.
    inversion H.
    SCase "le_n".
      apply le_n.
    SCase "le_S".
      inversion H1.
  Case "m = S m".
    intros.
    inversion H.
    SCase "le_n".
      apply le_n.
    SCase "le_S".
      apply IHm in H1.
      apply le_S.
      apply H1.
Qed.

Theorem le_plus_l :
  ∀ a b,
  a <= a + b.
Proof.
  intros.
  induction a.
  Case "a = 0".
    apply O_le_n.
  Case "a = S a".
    simpl.
    apply n_le_m__Sn_le_Sm.
    apply IHa.
Qed.

Theorem plus_lt :
  ∀ n1 n2 m,
  n1 + n2 < m →
  n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros.
  split.
  Case "S n1 <= m".
    induction n2.
    SCase "n2 = 0".
      rewrite <- PeanoNat.Nat.add_succ_l in H.
      rewrite PeanoNat.Nat.add_0_r in H.
      apply H.
    SCase "n2 = S n2".
      apply le_S in H.
      apply Sn_le_Sm__n_le_m in H.
      rewrite PeanoNat.Nat.add_succ_r in H.
      apply IHn2 in H.
      apply H.
  Case "S n2 <= m".
    induction n1.
    SCase "n1 = 0".
      rewrite <- PeanoNat.Nat.add_succ_r in H.
      rewrite PeanoNat.Nat.add_0_l in H.
      apply H.
    SCase "n1 = S n1".
      apply le_S in H.
      apply Sn_le_Sm__n_le_m in H.
      rewrite PeanoNat.Nat.add_succ_l in H.
      apply IHn1 in H.
      apply H.
Qed.

Theorem lt_S :
  ∀ n m,
  n < m →
  n < S m.
Proof.
  unfold lt.
  intros.
  apply le_S.
  apply H.
Qed.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.
Theorem ble_nat_true :
  ∀ n m,
  ble_nat n m = true ->
  n <= m.
Proof.
  induction n.
  Case "n = 0".
    intros.
    apply O_le_n.
  Case "n = S n".
    destruct m.
    SCase "m = 0".
      intros.
      inversion H.
    SCase "m = S m".
      intros.
      inversion H.
      apply IHn in H1.
      apply n_le_m__Sn_le_Sm in H1.
      apply H1.
Qed.

Theorem ble_nat_n_Sn_false :
  ∀ n m,
  ble_nat n (S m) = false ->
  ble_nat n m = false.
Proof.
  induction n.
  Case "n = 0".
    intros.
    inversion H.
  Case "n = S n".
    induction m.
    SCase "m = 0".
      intros.
      reflexivity.
    SCase "m = S m".
      intros.
      inversion H.
      rewrite H1.
      apply IHn in H1.
      inversion H1.
      reflexivity.
Qed.

Theorem ble_nat_false :
  ∀ n m,
  ble_nat n m = false ->
  ~(n <= m).
Proof.
  unfold not.
  induction n.
  Case "n = 0".
    intros.
    inversion H.
  Case "n = S n".
    induction m.
    SCase "m = 0".
      intros.
      inversion H0.
    SCase "m = S n".
      intros.
      simpl in H.
      apply IHn in H.
      apply H.
      apply Sn_le_Sm__n_le_m in H0.
      apply H0.
Qed.

(* 練習問題: ★★★, recommended (nostutter) *)
Inductive nostutter: list nat -> Prop :=
  | nostutter_nil : nostutter []
  | nostutter_cons_nil : forall (n : nat), nostutter [n]
  | nostutter_cons : forall (n lx : nat) (ls : list nat), nostutter (lx :: ls) -> n <> lx -> nostutter (n :: lx ::ls).

Example test_nostutter_1: nostutter [3, 1, 4, 1, 5, 6].
  apply nostutter_cons.
  apply nostutter_cons.
  apply nostutter_cons.
  apply nostutter_cons.
  apply nostutter_cons.
  apply nostutter_cons_nil.
  unfold not. intros. inversion H.
  unfold not. intros. inversion H.
  unfold not. intros. inversion H.
  unfold not. intros. inversion H.
  unfold not. intros. inversion H.
Qed.

Example test_nostutter_2: nostutter [].
  apply nostutter_nil.
Qed.

Example test_nostutter_3: nostutter [5].
  apply nostutter_cons_nil.
Qed.

Example test_nostutter_4: not (nostutter [3, 1, 1, 4]).
  unfold not.
  intros.
  inversion H.
  inversion H2.
  unfold not in H9.
  apply H9.
  reflexivity.
Qed.

(* 練習問題: ★★★★, optional (pigeonhole principle) *)
Lemma app_length :
  ∀ {X : Type} (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1.
  Case "l1: []".
    reflexivity.
  Case "l1: a :: l1".
    simpl.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma appears_in_app_split :
  ∀ {X : Type} (x : X) (l : list X),
  appears_in x l ->
  exists l1, exists l2,
  l = l1 ++ (x :: l2).
Proof.
  intros.
  induction l.
  Case "l: []".
    inversion H.
  Case "l: a :: l".
    inversion H.
    SCase "ai_here".
      apply ex_intro with (witness := []).
      apply ex_intro with (witness := l).
      reflexivity.
    SCase "ai_later".
      apply IHl in H1.
      inversion H1.
      inversion H3.
      apply ex_intro with (witness := a :: witness).
      apply ex_intro with (witness := witness0).
      simpl.
      assert (
        listeqcons:
          forall (X : Type) (x : X) (l1 l2 : list X),
          l1 = l2 -> x :: l1 = x :: l2
      ).
        intros.
        induction l1.
        SSCase "l1: []".
          rewrite <- H5.
          reflexivity.
        SSCase "l1: a :: l1".
          rewrite <- H5.
          reflexivity.
      apply listeqcons.
      apply H4.
Qed.

Inductive repeats {X : Type} : list X -> Prop :=
  | repeats_cons_repeated : forall (x : X) (l : list X), appears_in x l -> repeats (x :: l)
  | repeats_cons_other : forall (x : X) (l : list X), repeats l -> repeats (x :: l).

(* https://qiita.com/yoshihiro503/items/0233bf2ada9b8bfa00fa *)
Lemma lt_irrefl :
  forall n,
  ~ n < n.
Proof.
  induction n.
  Case "n = 0".
    intro.
    inversion H.
  Case "n = S n".
    intro.
    destruct IHn.
    apply Sn_le_Sm__n_le_m.
    apply H.
Qed.

Lemma lt_not_le:
  forall n m : nat,
  n < m ->
  ~ m <= n.
Proof.
  intros.
  induction H.  
  Case "le_n".
    apply lt_irrefl.
  Case "le_S".
    intro.
    destruct IHle.
    inversion H0.
    SCase "le_n".
      apply le_S.
      apply le_n.
    SCase "le_S".
      rewrite <- H2 in H0.
      apply le_S.
      apply Sn_le_Sm__n_le_m.
      apply H0.
Qed. 

Lemma aux1 :
  forall {X : Type} (x : X) xs l1 l2,
  (forall a, appears_in a (x :: xs) -> appears_in a (l1 ++ (x :: l2))) ->
  ~ repeats (x :: xs) ->
  forall a, appears_in a xs ->
  appears_in a (l1 ++ l2).
Proof.
  intros.
  specialize (ai_later a x xs H1).
  intros.
  apply H in H2.
  apply appears_in_app in H2.
  destruct H2.
  Case "appears_in a l1".
    apply app_appears_in.
    left.
    apply H2.
  Case "appears_in a (x :: l2)".
    apply app_appears_in.
    right.
    inversion H2.
    SCase "ai_here".
      destruct H0.
      rewrite <- H4.
      apply repeats_cons_repeated.
      apply H1.
    SCase "ai_later".
      apply H4.
Qed.

Lemma aux2 :
  forall {X : Type} xs ys,
  (forall a : X, appears_in a xs -> appears_in a ys) ->
  ~ repeats xs ->
  length xs <= length ys.
Proof.
  intros X xs.
  induction xs.
  Case "xs: []".
    intros.
    simpl.
    induction (length ys).
    SCase "length ys = 0".
      apply le_n.
    SCase "length ys = S length ys".
      apply le_S.
      apply IHn.
  Case "xs: a :: xs".
    intros.
    destruct (appears_in_app_split a ys (H a (ai_here a xs))) as [l1].
    destruct H1 as [l2].
    rewrite H1.
    rewrite app_length.
    simpl. 
    rewrite <- plus_n_Sm.
    apply n_le_m__Sn_le_Sm.
    rewrite <- app_length.
    apply IHxs.
    SCase "∀ a0 : X, appears_in a0 xs → appears_in a0 (l1 ++ l2)".
      intros.
      rewrite H1 in H.
      apply (aux1 a xs l1 l2 H H0).
      apply H2.
    SCase "~ repeats xs".
      intro.
      destruct H0.
      apply repeats_cons_other.
      apply H2.
Qed.

Theorem pigeonhole_principle: forall {X:Type} (l1 l2:list X),
  excluded_middle ->
  (forall x, appears_in x l1 -> appears_in x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros.

  (* 背理法 *)
  destruct (H (repeats l1)). apply H2.

  apply lt_not_le in H1.
  destruct H1.

  apply aux2.
  apply H0.
  apply H2.
Qed.

(********************************
  選択課題
*********************************)
(* TODO *)
