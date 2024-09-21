Require Import Unicode.Utf8.
Require Import commons.
Require Import Arith.
Require Import Lia.
Require Import ImpList_J.

(********************************
  ホーア論理
*********************************)

(* -----
  表明
-------- *)

Definition Assertion := state -> Prop.

(* 練習問題: ★ (assertions) *)
(*
fun st => asnat (st X) = 3
ある状態で、X = 3である。

fun st => asnat (st X) = x
ある状態でX = xである。

fun st => asnat (st X) <= asnat (st Y)
ある状態でX <= Yである。

fun st => asnat (st X) = 3 \/ asnat (st X) <= asnat (st Y)
ある状態でX = 3であるか、X <= Yである。

fun st => (asnat (st Z)) * (asnat (st Z)) <= x /\ ~ (((S (asnat (st Z))) * (S (asnat (st Z)))) <= x)
ある状態でZ^2 <= xかつ、(Z + 1)^2 < xである。

fun st => True
ある状態で常に真である。

fun st => False
ある状態で常に偽である。
*)

(* -----
  ホーアの三つ組
-------- *)

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
  c / st || st' ->
  P st ->
  Q st'.

Notation "{{ P }} c" :=
  (hoare_triple P c (fun st => True)) (at level 90).
Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

(* 練習問題: ★ (triples) *)
(*
{{True}} c {{X = 5}}
あらゆる状態でcが停止するならX = 5が成り立つ。

{{X = x}} c {{X = x + 5)}}
X = xが成り立つ状態でcが停止するならX = x + 5が成り立つ

{{X <= Y}} c {{Y <= X}}
X <= Yが成り立つ状態でcが停止するならY <= Xが成り立つ

{{True}} c {{False}}
あらゆる状態でcは停止しない

{{X = x}}
c
{{Y = real_fact x}}.
X = xが成り立つ状態でcが停止するならY = real_fact xが成り立つ

{{True}}
c
{{(Z * Z) <= x ∧ ~ (((S Z) * (S Z)) <= x)}} 
あらゆる状態でcが停止するなら(Z * Z) <= xかつ~ (((S Z) * (S Z)) <= x)が成り立つ
*)

(* 練習問題: ★ (valid_triples) *)
(*
{{True}} X ::= 5 {{X = 5}}
成り立つ

{{X = 2}} X ::= X + 1 {{X = 3}}
成り立つ

{{True}} X ::= 5; Y ::= 0 {{X = 5}}
成り立つ

{{X = 2 ∧ X = 3}} X ::= 5 {{X = 0}}
成り立つ

{{True}} SKIP {{False}}
成り立たない

{{False}} SKIP {{True}}
成り立つ

{{True}} WHILE True DO SKIP END {{False}}
成り立つ

{{X = 0}}
WHILE X == 0 DO X ::= X + 1 END
{{X = 1}}
成り立つ

{{X = 1}}
WHILE X <> 0 DO X ::= X + 1 END
{{X = 100}}
成り立つ
*)

Theorem hoare_post_true :
  forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.
Qed.

Theorem hoare_pre_false :
  forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.
Qed.

(* -----
  最弱事前条件
-------- *)

(* 練習問題: ★ (wp) *)
(*
{{ X = 5 }} SKIP {{ X = 5 }}

{{ Y + Z = 5 }} X ::= Y + Z {{ X = 5 }}

{{ True }} X ::= Y {{ X = Y }}

{{ (X = 0 /\ Z = 4) \/ (X <> 0 /\ W = 3) }}
IFB X == 0 THEN Y ::= Z + 1 ELSE Y ::= W + 2 FI
{{ Y = 5 }}

{{ False }}
X ::= 5
{{ X = 0 }}

{{ True }}
WHILE True DO X ::= 0 END
{{ X = 0 }} 
*)

(* -----
  証明規則
-------- *)

(* 代入 *)

Definition assn_sub V a Q : Assertion :=
  fun (st : state) =>
    Q (update st V (aeval st a)).

Theorem hoare_asgn :
  forall Q V a,
  {{assn_sub V a Q}} (V ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q V a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.
Qed.

Example assn_sub_example :
  {{fun st => 3 = 3}}
  (X ::= (ANum 3))
  {{fun st => asnat (st X) = 3}}.
Proof.
  assert ((fun st => 3 = 3) = (assn_sub X (ANum 3) (fun st => asnat (st X) = 3))).
  Case "Proof of assertion".
    unfold assn_sub. reflexivity.
  rewrite -> H. apply hoare_asgn.
Qed.

Theorem hoare_asgn_eq :
  forall Q Q' V a,
  Q' = assn_sub V a Q ->
  {{Q'}} (V ::= a) {{Q}}.
Proof.
  intros Q Q' V a H. rewrite H. apply hoare_asgn.
Qed.

Example assn_sub_example' :
  {{fun st => 3 = 3}}
  (X ::= (ANum 3))
  {{fun st => asnat (st X) = 3}}.
Proof.
  apply hoare_asgn_eq. reflexivity.
Qed.

(* 練習問題: ★★ (hoare_asgn_examples) *)
Example hoare_asgn_examples_1 :
  {{fun st => asnat (st X) + 1 <= 5}}
  (X ::= (APlus (AId X) (ANum 1)))
  {{fun st => asnat (st X) <= 5}}.
Proof.
  apply hoare_asgn_eq.
  unfold assn_sub.
  simpl.
  reflexivity.
Qed.

Example hoare_asgn_examples_2 :
  {{fun st => 0 <= 3 /\ 3 <= 5}}
  (X ::= (ANum 3))
  {{fun st => 0 <= asnat (st X) /\ asnat (st X) <= 5}}.
Proof.
  apply hoare_asgn_eq.
  unfold assn_sub.
  simpl.
  reflexivity.
Qed.

(* 練習問題: ★★★ (hoarestate2) *)
(*
以下のような前向きバージョンの規則を考える

------------------------------ (hoare_asgn')
{{ P }} V ::= a {{ P /\ V = a }} 

これは、
P: True
V: X
a: a
のときに以下の自然な三つ組を証明できるため、一見良さそうである。

{{ True }} X ::= a {{ True /\ X = a }} => {{ X = a }}

一方で、aにX自身が含まれる場合はうまく行かない。

{{ True }} X ::= X + 1 {{ True /\ X = X + 1 }} => {{ X = X + 1 }}

事後条件の中のX = X + 1は常に成り立たない。

したがって、この規則によって成り立たない三つ組を証明できてしまう。
*)

(* 練習問題: ★★★, optional (hoare_asgn_weakest) *)
Theorem hoare_asgn_weakest :
  forall P V a Q,
  {{P}} (V ::= a) {{Q}} ->
  forall st, P st -> assn_sub V a Q st.
Proof.
  intros P V a Q Htriple st Hpst.
  unfold assn_sub.
  unfold hoare_triple in Htriple.
  apply Htriple with (st := st).

  constructor.
  reflexivity.

  assumption.
Qed.

(* 帰結 *)

Theorem hoare_consequence :
  forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  (forall st, P st -> P' st) ->
  (forall st, Q' st -> Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  intros st st' Hc HP.
  apply HQ'Q. apply (Hht st st'). assumption.
  apply HPP'. assumption.
Qed.

Theorem hoare_consequence_pre :
  forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  (forall st, P st -> P' st) ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  apply hoare_consequence with (P' := P') (Q' := Q);
    try assumption.
  intros st H. apply H.
Qed.

Theorem hoare_consequence_post :
  forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  (forall st, Q' st -> Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  apply hoare_consequence with (P' := P) (Q' := Q');
    try assumption.
  intros st H. apply H.
Qed.

Example hoare_asgn_example1 :
  {{fun st => True}} (X ::= (ANum 1)) {{fun st => asnat (st X) = 1}}.
Proof.
  apply hoare_consequence_pre with (P' := (fun st => 1 = 1)).
  apply hoare_asgn_eq. reflexivity.
  intros st H. reflexivity.
Qed.

(* 余談: eapply タクティック *)

Example hoare_asgn_example1' :
  {{fun st => True}}
  (X ::= (ANum 1))
  {{fun st => asnat (st X) = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn_eq. reflexivity.
  intros st H. unfold assn_sub. reflexivity.
Qed.

(* Skip *)

Theorem hoare_skip :
  forall P,
  {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.
Qed.

(* コマンド合成 *)

Theorem hoare_seq :
  forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); try assumption.
Qed.

Example hoare_asgn_example3 :
  forall a n,
  {{fun st => aeval st a = n}}
  (X ::= a; SKIP)
  {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  Case "right part of seq".
    apply hoare_skip.
  Case "left part of seq".
    eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. subst. reflexivity.
Qed.

(* 練習問題: ★★ (hoare_asgn_example4) *)
Example hoare_asgn_example4 :
  {{fun st => True}}
  (
    X ::= (ANum 1);
    Y ::= (ANum 2)
  )
  {{fun st => asnat (st X) = 1 /\ asnat (st Y) = 2}}.
Proof.
  eapply hoare_seq.
  Case "right part of seq".
    apply hoare_asgn.
  Case "left part of seq".
    eapply hoare_consequence_pre.
    apply hoare_asgn.
    intros.
    unfold assn_sub.
    simpl.
    lia.
Qed.

(* 練習問題: ★★★, optional (swap_exercise) *)
Example swap_exercise :
  forall x y,
  {{fun st => asnat (st X) = x /\ asnat (st Y) = y}}
  (
    Z ::= (AId X);
    X ::= (AId Y);
    Y ::= (AId Z)
  )
  {{fun st => asnat (st X) = y /\ asnat (st Y) = x}}.
Proof.
  intros.
  eapply hoare_seq.
  Case "right part of seq".
    eapply hoare_seq.
    SCase "right part of seq".
      apply hoare_asgn.
    SCase "left part of seq".
      apply hoare_asgn.
  Case "left part of seq".
    eapply hoare_consequence_pre.
    apply hoare_asgn.
    intros.
    unfold assn_sub.
    unfold update.
    simpl.
    apply and_comm.
    assumption.
Qed.

(* 練習問題: ★★★, optional (hoarestate1) *)
(*
aに変数Xが含まれる場合があるからである。

例えば、
a: X
n: 0
である場合、

{{fun st => aeval st a = 0}}
(X ::= (ANum 3); Y ::= X)
{{fun st => asnat (st Y) = 0}}. 

となるが、事後条件におけるasnat (st Y)は3なので、3 = 0は成り立たない。
*)

(* 条件分岐 *)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true :
  forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.
Qed.

Lemma bexp_eval_false :
  forall b st,
  beval st b = false ->
  ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.
Qed.

Theorem hoare_if :
  forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  Case "b is true".
    apply (HTrue st st').
      assumption.
      split. assumption.
             apply bexp_eval_true. assumption.
  Case "b is false".
    apply (HFalse st st').
      assumption.
      split. assumption.
             apply bexp_eval_false. assumption.
Qed.

Example if_example :
  {{fun st => True}}
  IFB (BEq (AId X) (ANum 0))
    THEN (Y ::= (ANum 2))
    ELSE (Y ::= APlus (AId X) (ANum 1))
  FI
  {{fun st => asnat (st X) <= asnat (st Y)}}.
Proof.
  apply hoare_if.
  Case "Then".
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, update. simpl. intros.
    inversion H.
       apply Nat.eqb_eq in H1.
       rewrite H1. lia.
  Case "Else".
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub, update; simpl; intros. lia.
Qed.

(* ループ *)

Lemma hoare_while:
  forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember (WHILE b DO c END) as wcom.
  ceval_cases (induction He) Case; try (inversion Heqwcom); subst.

  Case "E_WhileEnd".
    split. assumption. apply bexp_eval_false. assumption.

  Case "E_WhileLoop".
    apply IHHe2. reflexivity.
    apply (Hhoare st st'); try assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

Example while_example :
  {{fun st => asnat (st X) <= 3}}
  WHILE
    (BLe (AId X) (ANum 2))
  DO
    X ::= APlus (AId X) (ANum 1)
  END
  {{fun st => asnat (st X) = 3}}.
Proof.
  eapply hoare_consequence_post.
  apply hoare_while.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold bassn, assn_sub. intros. rewrite update_eq. simpl.
     inversion H as [_ H0]. simpl in H0. apply Nat.leb_le in H0.
     lia.
  unfold bassn. intros. inversion H as [Hle Hb]. simpl in Hb.
     remember (Nat.leb (asnat (st X)) 2) as le. destruct le.
     apply ex_falso_quodlibet. apply Hb; reflexivity.
     symmetry in Heqle. apply Nat.leb_gt in Heqle. lia.
Qed.

Theorem always_loop_hoare:
  forall P Q,
  {{P}}
  WHILE BTrue DO SKIP END
  {{Q}}.
Proof.
  intros P Q.
  apply hoare_consequence_pre with (P' := fun st : state => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  Case "Loop body preserves invariant".
    apply hoare_post_true. intros st. apply I.
  Case "Loop invariant and negated guard imply postcondition".
    simpl. intros st [Hinv Hguard].
    apply ex_falso_quodlibet. apply Hguard. reflexivity.
  Case "Precondition implies invariant".
    intros st H. constructor.
Qed.

Print hoare_triple.

Theorem always_loop_hoare':
  forall P Q,
  {{P}}
  WHILE BTrue DO SKIP END
  {{Q}}.
Proof.
  unfold hoare_triple. intros P Q st st' contra.
  apply loop_never_stops in contra. inversion contra.
Qed.

(* 練習問題: REPEATのホーア規則 *)

Module RepeatExercise.
  (* 練習問題: ★★★★ (hoare_repeat) *)
  Inductive com : Type :=
    | CSkip : com
    | CAss : id -> aexp -> com
    | CSeq : com -> com -> com
    | CIf : bexp -> com -> com -> com
    | CWhile : bexp -> com -> com
    | CRepeat : com -> bexp -> com.

  Tactic Notation "com_cases" tactic(first) ident(c) :=
    first;
    [
        Case_aux c "SKIP"
      | Case_aux c "::="
      | Case_aux c ";"
      | Case_aux c "IFB"
      | Case_aux c "WHILE"
      | Case_aux c "CRepeat"
  ].

  Notation "'SKIP'" :=
    CSkip.
  Notation "c1 ; c2" :=
    (CSeq c1 c2) (at level 80, right associativity).
  Notation "X '::=' a" :=
    (CAss X a) (at level 60).
  Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80, right associativity).
  Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
    (CIf e1 e2 e3) (at level 80, right associativity).
  Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
    (CRepeat e1 b2) (at level 80, right associativity).

  Inductive ceval : state -> com -> state -> Prop :=
    | E_Skip :
      forall st,
        ceval st SKIP st
    | E_Ass :
      forall st a1 n V,
        aeval st a1 = n ->
        ceval st (V ::= a1) (update st V n)
    | E_Seq :
      forall c1 c2 st st' st'',
        ceval st c1 st' ->
        ceval st' c2 st'' ->
        ceval st (c1 ; c2) st''
    | E_IfTrue :
      forall st st' b1 c1 c2,
        beval st b1 = true ->
        ceval st c1 st' ->
        ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
    | E_IfFalse :
      forall st st' b1 c1 c2,
        beval st b1 = false ->
        ceval st c2 st' ->
        ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
    | E_WhileEnd :
      forall b1 st c1,
        beval st b1 = false ->
        ceval st (WHILE b1 DO c1 END) st
    | E_WhileLoop :
      forall st st' st'' b1 c1,
        beval st b1 = true ->
        ceval st c1 st' ->
        ceval st' (WHILE b1 DO c1 END) st'' ->
        ceval st (WHILE b1 DO c1 END) st''
    | E_RepeatEnd :
      forall st c1 st' b1,
        ceval st c1 st' ->
        beval st' b1 = true ->
        ceval st (REPEAT c1 UNTIL b1 END) st'
    | E_RepeatLoop :
      forall st c1 st' b1 st'',
        ceval st c1 st' ->
        beval st' b1 = false ->
        ceval st' (REPEAT c1 UNTIL b1 END) st'' ->
        ceval st (REPEAT c1 UNTIL b1 END) st''.

  Tactic Notation "ceval_cases" tactic(first) ident(c) :=
    first;
    [
        Case_aux c "E_Skip"
      | Case_aux c "E_Ass"
      | Case_aux c "E_Seq"
      | Case_aux c "E_IfTrue"
      | Case_aux c "E_IfFalse"
      | Case_aux c "E_WhileEnd"
      | Case_aux c "E_WhileLoop"
      | Case_aux c "E_RepeatEnd"
      | Case_aux c "E_RepeatLoop"
    ].

  Notation "c1 '/' st '||' st'" :=
    (ceval st c1 st') (at level 40, st at level 39).
  Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion): Prop :=
    forall st st',
    (c / st || st') ->
    P st -> Q st'.
  Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q) (at level 90, c at next level).

  Lemma hoare_repeat:
    forall P b c,
    {{P}} c {{P}} ->
    {{P}} REPEAT c UNTIL b END {{fun st => P st /\ bassn b st}}.
  Proof.
    intros P b c Htriple.
    unfold hoare_triple.
    intros st st' Heval Hpst.
    unfold hoare_triple in Htriple.
    remember (REPEAT c UNTIL b END) as com.
    ceval_cases (induction Heval) Case; intros;
      try solve [
        inversion Heqcom
      ].

    Case "E_RepeatEnd".
      inversion Heqcom; subst.
      split.
      apply (Htriple st st'); assumption.
      unfold bassn.
      assumption.

    Case "E_RepeatLoop".
      apply IHHeval2.
      assumption.
      inversion Heqcom; subst.
      apply (Htriple st st'); assumption.
  Qed.
End RepeatExercise.

(* -----
  修飾付きプログラム
-------- *)

(********************************
  ホーア論理によるプログラムについての推論
*********************************)

(* -----
  例: 遅い引き算
-------- *)
Definition subtract_slowly : com :=
  WHILE
    BNot (BEq (AId X) (ANum 0))
  DO
    Z ::= AMinus (AId Z) (ANum 1);
    X ::= AMinus (AId X) (ANum 1)
  END.

Definition subtract_slowly_invariant x z :=
  fun st => minus (asnat (st Z)) (asnat (st X)) = minus z x.

Theorem subtract_slowly_correct:
  forall x z,
  {{fun st => asnat (st X) = x /\ asnat (st Z) = z}}
  subtract_slowly
  {{fun st => asnat (st Z) = minus z x}}.
Proof.
  intros x z. unfold subtract_slowly.
  eapply hoare_consequence with (P' := subtract_slowly_invariant x z).
  apply hoare_while.

  Case "Loop body preserves invariant".
    eapply hoare_seq. apply hoare_asgn.
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold subtract_slowly_invariant, assn_sub, update, bassn. simpl.
    intros st [Inv GuardTrue].
    remember (Nat.eqb (asnat (st X)) 0) as Q; destruct Q.
     inversion GuardTrue.
     symmetry in HeqQ. apply Nat.eqb_neq in HeqQ. lia.
  Case "Initial state satisfies invariant".
    unfold subtract_slowly_invariant.
    intros st [HX HZ]. lia.
  Case "Invariant and negated guard imply postcondition".
    intros st [Inv GuardFalse].
    unfold subtract_slowly_invariant in Inv.
    unfold bassn in GuardFalse. simpl in GuardFalse.
    destruct (asnat (st X)).
      lia.
      apply ex_falso_quodlibet. apply GuardFalse. reflexivity.
Qed.

(* -----
  練習問題: ゼロへの簡約
-------- *)

(* 練習問題: ★★ (reduce_to_zero_correct) *)
Definition reduce_to_zero : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= AMinus (AId X) (ANum 1)
  END.

Theorem reduce_to_zero_correct :
  {{fun st => True}}
  reduce_to_zero
  {{fun st => asnat (st X) = 0}}.
Proof.
  unfold reduce_to_zero.
  eapply hoare_consequence_post.
  eapply hoare_while.

  Case "{{P ∧ b}} c {{P}}".
    eapply hoare_consequence_pre.
    apply hoare_asgn.
    unfold bassn, assn_sub.
    intros.
    constructor.
  Case "{{P ∧ ~b}} -> ~b".
    unfold bassn.
    simpl.
    intros.
    inversion H.
    apply Bool.eq_true_negb_classical in H1.
    apply Nat.eqb_eq in H1.
    assumption.
Qed.

(* -----
  練習問題: 遅い足し算
-------- *)

Definition add_slowly : com :=
  WHILE
    BNot (BEq (AId X) (ANum 0))
  DO
    Z ::= APlus (AId Z) (ANum 1);
    X ::= AMinus (AId X) (ANum 1)
  END.

(* 練習問題: ★★★ (add_slowly_decoration) *)
(*
{{ Z = z /\ X = x }} =>
{{ Z + X = z + x }}
WHILE
  BNot (BEq (AId X) (ANum 0))
DO
  {{ Z + X = z + x /\ X <> 0 }} =>
  {{ (Z + 1) + (X - 1) = z + x }}
  Z ::= APlus (AId Z) (ANum 1);
  {{ Z + (X - 1) = z + x }}
  X ::= AMinus (AId X) (ANum 1)
  {{ Z + X = z + x }}
END
{{ Z + X = z + x /\ X = 0 }} =>
{{ Z = z + x }}
*)

(* 練習問題: ★★★ (add_slowly_formal) *)

Definition add_slowly_invariant x z :=
  fun st => asnat (st Z) + asnat (st X) = z + x.

Theorem add_slowly_correct :
  forall x z,
  {{ fun st => asnat (st Z) = z /\ asnat (st X) = x }}
  add_slowly
  {{ fun st => asnat (st Z) = z + x }}.
Proof.
  intros.
  eapply hoare_consequence with (P' := (add_slowly_invariant x z)).
  apply hoare_while.

  Case "while body preserves P".
    eapply hoare_consequence_pre.
    eapply hoare_seq.
    
    SCase "X ::= X - 1".
      apply hoare_asgn.

    SCase "Z ::= Z + 1".
      apply hoare_asgn.

    SCase "{{ Z + X = z + x /\ X <> 0 }} => {{ (Z + 1) + (X - 1) = z + x }}".
      unfold add_slowly_invariant, bassn, assn_sub.
      simpl.
      intros.
      rewrite (update_neq Z X _ _).
      rewrite Nat.add_sub_assoc.

      lia.

      inversion H.
      apply Bool.eq_true_not_negb_iff in H1.
      apply Bool.not_true_iff_false in H1.
      apply Nat.eqb_neq in H1.
      lia.

      reflexivity.

  Case "{{ Z = z /\ X = x }} => {{ Z + X = z + x }}".
    unfold add_slowly_invariant.
    lia.

  Case "{{ Z + X = z + x /\ X = 0 }} => {{ Z = z + x }}".
    unfold add_slowly_invariant, bassn, beval, aeval.
    intros.
    inversion H.
    apply Bool.eq_true_negb_classical in H1.
    apply Nat.eqb_eq in H1.
    simpl in H1.
    lia.
Qed.

(* -----
  例: パリティ
-------- *)

Definition find_parity : com :=
  Y ::= (ANum 0);
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    Y ::= AMinus (ANum 1) (AId Y);
    X ::= AMinus (AId X) (ANum 1)
  END.

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS:
      forall n : nat,
      ev n ->
      ev (S (S n)).
Definition find_parity_invariant x :=
  fun st =>
    asnat (st X) <= x /\
    (
      asnat (st Y) = 0 /\
      ev (x - asnat (st X)) \/ asnat (st Y) = 1 /\
      ~ev (x - asnat (st X))
    ).

Lemma not_ev_ev_S_gen:
  forall n,
  (~ ev n -> ev (S n)) /\
  (~ ev (S n) -> ev (S (S n))).
Proof.
  induction n as [| n'].
  Case "n = 0".
    split; intros H.
    SCase "->".
      apply ex_falso_quodlibet. apply H. apply ev_0.
    SCase "<-".
      apply ev_SS. apply ev_0.
  Case "n = S n'".
    inversion IHn' as [Hn HSn]. split; intros H.
    SCase "->".
      apply HSn. apply H.
    SCase "<-".
      apply ev_SS. apply Hn. intros contra.
      apply H. apply ev_SS. apply contra.
Qed.

Lemma not_ev_ev_S:
  forall n,
  ~ ev n -> ev (S n).
Proof.
  intros n.
  destruct (not_ev_ev_S_gen n) as [H _].
  apply H.
Qed.

Theorem ev_not_ev_S:
  forall n,
  ev n -> ~ ev (S n).
Proof.
Admitted.
Theorem find_parity_correct:
  forall x,
  {{fun st => asnat (st X) = x}}
  find_parity
  {{fun st => asnat (st Y) = 0 <-> ev x}}.
Proof.
  intros x. unfold find_parity.
  apply hoare_seq with (Q := find_parity_invariant x).
  eapply hoare_consequence.
  apply hoare_while with (P := find_parity_invariant x).
  Case "Loop body preserves invariant".
    eapply hoare_seq.
    apply hoare_asgn.
    eapply hoare_consequence_pre.
    apply hoare_asgn.
    intros st [[Inv1 Inv2] GuardTrue].
    unfold find_parity_invariant, bassn, assn_sub, aeval in *.
    rewrite update_eq.
    rewrite (update_neq Y X); auto.
    rewrite (update_neq X Y); auto.
    rewrite update_eq.
    simpl in GuardTrue. destruct (asnat (st X)).
      inversion GuardTrue. simpl.
    split. lia.
    inversion Inv2 as [[H1 H2] | [H1 H2]]; rewrite H1;
                     [right|left]; (split; simpl; [lia |]).
    apply ev_not_ev_S in H2.
    replace (S (x - S n)) with (x-n) in H2 by lia.
    rewrite Nat.sub_0_r. assumption.
    apply not_ev_ev_S in H2.
    replace (S (x - S n)) with (x - n) in H2 by lia.
    rewrite Nat.sub_0_r. assumption.
  Case "Precondition implies invariant".
    intros st H. assumption.
  Case "Invariant implies postcondition".
    unfold bassn, find_parity_invariant. simpl.
    intros st [[Inv1 Inv2] GuardFalse].
    destruct (asnat (st X)).
      split; intro.
        inversion Inv2.
           inversion H0 as [_ H1]. replace (x-0) with x in H1 by lia.
           assumption.
           inversion H0 as [H0' _]. rewrite H in H0'. inversion H0'.
        inversion Inv2.
           inversion H0. assumption.
           inversion H0 as [_ H1]. replace (x-0) with x in H1 by lia.
           apply ex_falso_quodlibet. apply H1. assumption.
      apply ex_falso_quodlibet. apply GuardFalse. reflexivity.
  Case "invariant established before loop".
    eapply hoare_consequence_pre.
    apply hoare_asgn.
    intros st H.
    unfold assn_sub, find_parity_invariant, update. simpl.
    subst.
    split.
    lia.
    replace (asnat (st X) - asnat (st X)) with 0 by lia.
    left. split. reflexivity.
    apply ev_0.
Qed.

(* 練習問題: ★★★ (wrong_find_parity_invariant) *)
Definition find_parity_invariant' x :=
  fun st =>
    (asnat (st Y)) = 0 <-> ev (x - asnat (st X)).

(*
オリジナルとの主な違いそれぞれについて、証明が成り立たない理由を述べる。

1. X <= xがない。

ループのBody内部では、X <= xであることがわからないためうまくいかない。

もしオリジナルにX <= xがない場合、ループBodyの冒頭では以下の表明が成り立っていることになるが、

{{
  (
    Y = 0 /\ ev (x - X)
    \/
    Y = 1 /\ ~ ev (x - X)
  ) /\
  X <> 0
}}

ここでY = 1でX > xの状態で成り立っているかもしれず、これは自然数の減算としては不正であり、意図した状態ではない。

2. Y = 1 /\ ~ ev (x - X)のケースがなく、/\の代わりに<->を使用している（「Y = 0 /\ ev (x - X)」ではなく「Y = 0 <-> ev (x - X)」となっている）

Y <> 0の場合についての情報がないためうまくいかない。

間違った定義ではループの冒頭で以下が成り立つ。

{{
  X <= x /\
  Y = 0 <-> ev (x - X) /\
  X <> 0
}}

ここで、Y = 2かつ~ ev (x - X)の状態で成り立っているかもしれず、これは意図した状態ではない。
*)

(* -----
  例: 平方根の探索
-------- *)

Definition sqrt_loop : com :=
  WHILE
    BLe
      (AMult
        (APlus (ANum 1) (AId Z))
        (APlus (ANum 1) (AId Z))
      )
      (AId X)
  DO
    Z ::= APlus (ANum 1) (AId Z)
  END.

Definition sqrt_com : com :=
  Z ::= ANum 0;
  sqrt_loop.

Definition sqrt_spec (x : nat) : Assertion :=
  fun st =>
    ((asnat (st Z)) * (asnat (st Z))) <= x /\
    ~ (
      ((S (asnat (st Z))) * (S (asnat (st Z)))) <= x
    ).

Definition sqrt_inv (x : nat) : Assertion :=
  fun st =>
    asnat (st X) = x /\
    ((asnat (st Z)) * (asnat (st Z))) <= x.

Theorem random_fact_1:
  forall st,
  (S (asnat (st Z))) * (S (asnat (st Z))) <= asnat (st X) ->
  bassn
    (BLe
      (AMult
        (APlus (ANum 1) (AId Z))
        (APlus (ANum 1) (AId Z))
      )
      (AId X)
    )
    st.
Proof.
  intros st Hle. unfold bassn. simpl.
  destruct (asnat (st X)) as [|x'].
  Case "asnat (st X) = 0".
    inversion Hle.
  Case "asnat (st X) = S x'".
    simpl in Hle. apply le_S_n in Hle.
    remember (
      Nat.leb
        (plus
          (asnat (st Z))
          (
            (asnat (st Z)) * (S (asnat (st Z)))
          )
        )
        x'
    ) as ble.
    destruct ble. reflexivity.
    symmetry in Heqble. apply Nat.leb_nle in Heqble.
    unfold not in Heqble. apply Heqble in Hle. inversion Hle.
Qed.

Theorem random_fact_2:
  forall st,
  bassn
    (BLe
      (AMult
        (APlus (ANum 1) (AId Z))
        (APlus (ANum 1) (AId Z))
      )
      (AId X)
    )
    st ->
    asnat (aeval st (APlus (ANum 1) (AId Z))) *
    asnat (aeval st (APlus (ANum 1) (AId Z))) <= asnat (st X).
Proof.
  intros st Hble. unfold bassn in Hble. simpl in *.
  destruct (asnat (st X)) as [| x'].
  Case "asnat (st X) = 0".
    inversion Hble.
  Case "asnat (st X) = S x'".
    apply Nat.leb_le in Hble. lia.
Qed.

Theorem sqrt_com_correct:
  forall x,
  {{fun st => True}}
  (X ::= ANum x; sqrt_com)
  {{sqrt_spec x}}.
Proof.
  intros x.
  apply hoare_seq with (Q := fun st => asnat (st X) = x).
  Case "sqrt_com".
    unfold sqrt_com.
    apply hoare_seq with (
      Q := fun st => asnat (st X) = x /\ asnat (st Z) = 0
    ).

    SCase "sqrt_loop".
      unfold sqrt_loop.
      eapply hoare_consequence.
      apply hoare_while with (P := sqrt_inv x).

      SSCase "loop preserves invariant".
        eapply hoare_consequence_pre.
        apply hoare_asgn. intros st H.
        unfold assn_sub. unfold sqrt_inv in *.
        inversion H as [[HX HZ] HP]. split.
        SSSCase "X is preserved".
          rewrite update_neq; auto.
        SSSCase "Z is updated correctly".
          rewrite (update_eq (aeval st (APlus (ANum 1) (AId Z))) Z st).
          subst. apply random_fact_2. assumption.

      SSCase "invariant is true initially".
        intros st H. inversion H as [HX HZ].
        unfold sqrt_inv. split. assumption.
        rewrite HZ. simpl. lia.

      SSCase "after loop, spec is satisfied".
        intros st H. unfold sqrt_spec.
        inversion H as [HX HP].
        unfold sqrt_inv in HX. inversion HX as [HX' Harith].
        split. assumption.
        intros contra. apply HP. clear HP.
        simpl. simpl in contra.
        apply random_fact_1. subst x. assumption.

    SCase "Z set to 0".
      eapply hoare_consequence_pre. apply hoare_asgn.
      intros st HX.
      unfold assn_sub. split.
      rewrite update_neq; auto.
      rewrite update_eq; auto.

  Case "assignment of X".
    eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H.
    unfold assn_sub. rewrite update_eq; auto.
Qed.

(* 練習問題: ★★★, optional (sqrt_informal) *)

(*
{{ True }} =>
{{ x = x /\ 0 = 0}}
X ::= ANum x;
{{ X = x /\ 0 = 0 }}
Z ::= ANum 0;
{{ X = x /\ Z = 0 }} =>
{{ X = x /\ Z^2 <= x }}
WHILE
  BLe
    (AMult
      (APlus (ANum 1) (AId Z))
      (APlus (ANum 1) (AId Z))
    )
    (AId X)
DO
  {{ X = x /\ Z^2 <= x /\ (Z + 1)^2 <= X }}
  Z ::= APlus (ANum 1) (AId Z)
  {{ X = x /\ Z^2 <= x }}
END
{{ X = x /\ Z^2 <= x /\ ~ ((Z + 1)^2 <= X) }} =>
{{ Z^2 <= x /\ ~ ((Z + 1)^2 <= x) }}
*)

(* -----
  練習問題: 階乗
-------- *)
Module Factorial.
  Fixpoint real_fact (n : nat) : nat :=
    match n with
    | O => 1
    | S n' => n * (real_fact n')
    end.

  Definition fact_body : com :=
    Y ::= AMult (AId Y) (AId Z);
    Z ::= AMinus (AId Z) (ANum 1).

  Definition fact_loop : com :=
    WHILE BNot (BEq (AId Z) (ANum 0)) DO
      fact_body
    END.

  Definition fact_com : com :=
    Z ::= (AId X);
    Y ::= ANum 1;
    fact_loop.

  (* 練習問題: ★★★, optional (fact_informal) *)
  (*
    {{ X = x }} =>
    {{ X = x /\ X = X /\ 1 = 1 }}
    Z ::= X;
    {{ X = x /\ Z = X /\ 1 = 1 }}
    Y ::= 1;
    {{ X = x /\ Z = X /\ Y = 1 }} =>
    {{ Y * real_fact Z = real_fact x }}
    WHILE Z <> 0 DO
      {{ Y * real_fact Z = real_fact x /\ Z <> 0 }} =>
      {{ (Y * Z) * real_fact (Z - 1) = real_fact x }}
      Y ::= Y * Z;
      {{ Y * real_fact (Z - 1) = real_fact x }}
      Z ::= Z - 1
      {{ Y * real_fact Z = real_fact x }}
    END
    {{ Y * real_fact Z = real_fact x /\ ~ (Z <> 0) }} =>
    {{ Y = real_fact x }} 
  *)

  (* 練習問題: ★★★★, optional (fact_formal) *)
  Definition fact_invariant (x : nat) : Assertion :=
    fun st =>
      (asnat (st Y)) * real_fact (asnat (st Z)) = real_fact x.

  Lemma real_fact_pre :
    forall n,
    n <> 0 ->
    n * real_fact (n - 1) = real_fact n.
  Proof.
    intros.
    destruct n.

    Case "n = 0".
      apply ex_falso_quodlibet.
      apply H.
      reflexivity.

    Case "n <> 0".
      simpl.
      rewrite Nat.sub_0_r.
      reflexivity.
  Qed.

  Theorem fact_com_correct:
    forall x,
    {{fun st => asnat (st X) = x}}
    fact_com
    {{fun st => asnat (st Y) = real_fact x}}.
  Proof.
    intros.
    unfold fact_com.
    eapply hoare_seq.
    apply hoare_seq with (Q := (fact_invariant x)).

    Case "fact_loop".
      unfold fact_loop.
      eapply hoare_consequence_post.
      apply hoare_while.

      SCase "fact_body".
        eapply hoare_consequence_pre.
        unfold fact_body.
        eapply hoare_seq.
        apply hoare_asgn.
        apply hoare_asgn.

        intros.
        inversion H as [Hfinv Hb].
        unfold fact_invariant, assn_sub, bassn, beval in *.
        simpl in *.
        rewrite update_neq.

        apply Bool.negb_true_iff in Hb.
        apply Nat.eqb_neq in Hb.

        rewrite <- Nat.mul_assoc.
        rewrite (real_fact_pre (asnat (st Z)) Hb).
        assumption.

        reflexivity.

      SCase "{{ Y * real_fact Z = real_fact x /\ ~ (Z <> 0) }} => {{ Y = real_fact x }}".
        intros.
        inversion H as [Hfinv Hnotb].
        unfold fact_invariant, not, bassn, beval in *.
        simpl in *.

        apply Bool.eq_true_negb_classical in Hnotb.
        apply Nat.eqb_eq in Hnotb.

        rewrite Hnotb in Hfinv.
        simpl in Hfinv.
        lia.

    Case "Y ::= 1".
      apply hoare_consequence_post with (
        Q' :=
          fun st =>
            asnat (st X) = x /\ asnat (st Z) = asnat (st X) /\ asnat (st Y) = 1 
      ).
      
      apply hoare_asgn.

      intros.
      inversion H as [HXx Htmp]; clear H.
      inversion Htmp as [HZX HY1]; clear Htmp.
      unfold fact_invariant.
      rewrite HY1.
      rewrite HZX.
      rewrite HXx.
      lia.

    Case "Z ::= X".
      eapply hoare_consequence_pre.
      apply hoare_asgn.

      intros.
      unfold assn_sub.
      simpl.
      rewrite update_neq.
      rewrite update_neq.
      rewrite update_neq.
      rewrite update_eq.

      repeat split;
      try solve [
        reflexivity
      ];
      try solve [
        assumption
      ].

      reflexivity.
      reflexivity.
      reflexivity.
  Qed.
End Factorial.

(* -----
  リストを扱うプログラムについての推論
-------- *)

(* 練習問題: ★★★ (list_sum) *)
Definition sum l := fold_right plus 0 l.

Definition sum_program :=
  Y ::= ANum 0;
  WHILE (BIsCons (AId X)) DO
    Y ::= APlus (AId Y) (AHead (AId X)) ;
    X ::= ATail (AId X)
  END.

Definition sum_program_spec := forall l,
  {{ fun st => aslist (st X) = l }}
  sum_program
  {{ fun st => asnat (st Y) = sum l }}.

(*
{{ X = l }} =>
{{ X = l /\ 0 = 0 }}
Y ::= ANum 0;
{{ X = l /\ Y = 0 }} =>
{{ Y + sum X = sum l }}
WHILE (BIsCons (AId X)) DO
  {{ Y + sum X = sum l /\ BIsCons (AId X) }} =>
  {{ (Y + AHead X) + sum (ATail X) = sum l }}
  Y ::= APlus (AId Y) (AHead (AId X)) ;
  {{ Y + sum (ATail X) = sum l }}
  X ::= ATail (AId X)
  {{ Y + sum X = sum l }}
END.
{{ Y + sum X = sum l /\ ~ BIsCons (AId X) }} =>
{{ Y = sum l }}.
*)

Definition list_member :=
  WHILE BIsCons (AId X) DO
    IFB (BEq (AId Y) (AHead (AId X))) THEN
      Z ::= (ANum 1)
    ELSE
      SKIP
    FI;
    X ::= ATail (AId X)
  END.

Inductive appears_in (n : nat) : list nat -> Prop :=
  | ai_here: forall l, appears_in n (n :: l)
  | ai_later: forall m l, appears_in n l -> appears_in n (m :: l).

Definition list_member_spec := forall l n,
  {{ fun st => st X = VList l /\ st Y = VNat n /\ st Z = VNat 0 }}
  list_member
  {{ fun st => st Z = VNat 1 <-> appears_in n l }}.

Fixpoint snoc {X : Type} (l : list X) (v : X) : (list X) :=
  match l with
  | nil => [ v ]
  | cons h t => h :: (snoc t v)
  end.

Lemma snoc_equation:
  forall (A : Type) (h : A) (x y : list A),
  snoc x h ++ y = x ++ h :: y.
Proof.
  intros A h x y.
  induction x.
    Case "x = []". reflexivity.
    Case "x = cons". simpl. rewrite IHx. reflexivity.
Qed.

Lemma appears_in_snoc1:
  forall a l,
  appears_in a (snoc l a).
Proof.
  induction l.
    Case "l = []". apply ai_here.
    Case "l = cons". simpl. apply ai_later. apply IHl.
Qed.

Lemma appears_in_snoc2:
  forall a b l,
  appears_in a l ->
  appears_in a (snoc l b).
Proof.
  induction l; intros H; inversion H; subst; simpl.
    Case "l = []". apply ai_here.
    Case "l = cons". apply ai_later. apply IHl. assumption.
Qed.

Lemma appears_in_snoc3:
  forall a b l,
   appears_in a (snoc l b) ->
   (appears_in a l \/ a = b).
Proof.
   induction l; intros H.
   Case "l = []". inversion H.
     SCase "ai_here". right. reflexivity.
     SCase "ai_later". left. assumption.
   Case "l = cons". inversion H; subst.
     SCase "ai_here". left. apply ai_here.
     SCase "ai_later". destruct (IHl H1).
       left. apply ai_later. assumption.
       right. assumption.
Qed.

Lemma append_singleton_equation:
  forall (x : nat) l l',
  (l ++ [x]) ++ l' = l ++ x :: l'.
Proof.
  intros x l l'.
  induction l.
    reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Lemma append_nil:
  forall (A : Type) (l : list A),
  l ++ [] = l.
Proof.
  induction l.
    reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Lemma beq_true__eq:
  forall n n',
  Nat.eqb n n' = true ->
  n = n'.
Proof.
  induction n; destruct n'.
  Case "n = 0, n' = 0". reflexivity.
  Case "n = 0, n' = S _". simpl. intros H. inversion H.
  Case "n = S, n' = 0". simpl. intros H. inversion H.
  Case "n = S, n' = S". simpl. intros H. rewrite (IHn n' H). reflexivity.
Qed.

Lemma beq_nat_refl:
  forall n,
  Nat.eqb n n = true.
Proof.
  induction n.
    reflexivity.
    simpl. assumption.
Qed.

Theorem list_member_correct:
  forall l n,
  {{ fun st => st X = VList l /\ st Y = VNat n /\ st Z = VNat 0 }}
  list_member
  {{ fun st => st Z = VNat 1 <-> appears_in n l }}.
Proof.
  intros l n.
  eapply hoare_consequence.
  apply hoare_while with (
    P :=
      fun st =>
        st Y = VNat n /\
        exists p, p ++ aslist (st X) = l /\
        (st Z = VNat 1 <-> appears_in n p)
      ).
    eapply hoare_seq.
    apply hoare_asgn.
    apply hoare_if.
    Case "If taken".
      eapply hoare_consequence_pre.
      apply hoare_asgn.
      intros st [[[H1 [p [H2 H3]]] H9] H10].
      unfold assn_sub. split.
        rewrite update_neq; try reflexivity.
        rewrite update_neq; try reflexivity.
        assumption.
        remember (aslist (st X)) as x.
        destruct x as [|h x'].
          unfold bassn in H9. unfold beval in H9. unfold aeval in H9.
          rewrite <- Heqx in H9. inversion H9.

          exists (snoc p h).
          rewrite update_eq.
          unfold aeval. rewrite update_neq; try reflexivity.
          rewrite <- Heqx.
          split.
            rewrite snoc_equation. assumption.

            rewrite update_neq; try reflexivity.
            rewrite update_eq.
            split.
              simpl.
              unfold bassn in H10. unfold beval in H10.
              unfold aeval in H10. rewrite H1 in H10.
              rewrite <- Heqx in H10. simpl in H10.
              rewrite (beq_true__eq _ _ H10).
              intros. apply appears_in_snoc1.

              intros. reflexivity.
    Case "If not taken".
      eapply hoare_consequence_pre. apply hoare_skip.
      unfold assn_sub.
      intros st [[[H1 [p [H2 H3]]] H9] H10].
      split.
        rewrite update_neq; try reflexivity.
        assumption.
        remember (aslist (st X)) as x.
        destruct x as [|h x'].
          unfold bassn in H9. unfold beval in H9. unfold aeval in H9.
          rewrite <- Heqx in H9. inversion H9.

          exists (snoc p h).
          split.
            rewrite update_eq.
            unfold aeval. rewrite <- Heqx.
            rewrite snoc_equation. assumption.

            rewrite update_neq; try reflexivity.
            split.
              intros. apply appears_in_snoc2. apply H3. assumption.

              intros. destruct (appears_in_snoc3 _ _ _ H).
              SCase "later".
                inversion H3 as [_ H3'].
                apply H3'. assumption.
              SCase "here (absurd)".
                subst.
                unfold bassn in H10. unfold beval in H10. unfold aeval in H10.
                rewrite <- Heqx in H10. rewrite H1 in H10.
                simpl in H10. rewrite beq_nat_refl in H10.
                apply ex_falso_quodlibet. apply H10. reflexivity.
  intros st [H1 [H2 H3]].
  rewrite H1. rewrite H2. rewrite H3.
  split.
    reflexivity.
    exists []. split.
      reflexivity.
      split; intros H; inversion H.
  simpl. intros st [[H1 [p [H2 H3]]] H5].
  unfold bassn in H5. unfold beval in H5. unfold aeval in H5.
  destruct (aslist (st X)) as [|h x'].
    rewrite append_nil in H2.
    rewrite <- H2.
    assumption.

    apply ex_falso_quodlibet. apply H5. reflexivity.
Qed.

(* 練習問題: ★★★★, optional (list_reverse) *)
Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => []
  | cons h t => snoc (rev t) h
  end.

Definition list_reverse_program :=
  WHILE
    (BIsCons (AId X))
  DO
    Y ::= ACons (AHead (AId X)) (AId Y);
    X ::= ATail (AId X)
  END.

Lemma rev_equation:
  forall (A : Type) (h : A) (x y : list A),
  rev (h :: x) ++ y = rev x ++ h :: y.
Proof.
  intros. simpl. apply snoc_equation.
Qed.

(*
{{ X = l ∧ Y = nil }}
{{ exists p, (p ++ X = l /\ rev X ++ Y = rev l) }}
WHILE
  (BIsCons (AId X))
DO
  {{ exists p, (p ++ X = l /\ rev X ++ Y = rev l) /\ BIsCons X }} =>
  {{ exists p, (p ++ (ATail X) = l /\ rev (ATail X) ++ (ACons (AHead X) Y) = rev l) }}
  Y ::= ACons (AHead (AId X)) (AId Y);
  {{ exists p, (p ++ (ATail X) = l /\ rev (ATail X) ++ Y = rev l) }}
  X ::= ATail (AId X)
  {{ exists p, (p ++ X = l /\ rev X ++ Y = rev l) }}
END
{{ (exists p, (p ++ X = l /\ rev X ++ Y = rev l)) /\ ~ BIsCons (AId X) }}
{{ Y = rev l }}
*)

Definition list_reverse_invariant (l : list nat) : Assertion :=
  fun st =>
    exists p, (p ++ aslist (st X) = l /\ rev (aslist (st X)) ++ aslist (st Y) = rev l).

Lemma head_tail :
  forall l,
  l <> nil ->
  head l :: tail l = l.
Proof.
  intros.
  destruct l.
  Case "l = []".
    apply ex_falso_quodlibet.
    apply H.
    reflexivity.
  Case "l: n :: l".
    simpl.
    reflexivity.
Qed.

Theorem list_reverse_correct :
  forall l : list nat,
  {{ fun st => aslist (st X) = l /\ aslist (st Y) = nil }}
  list_reverse_program
  {{ fun st => aslist (st Y) = rev l }}.
Proof.
  intros.
  apply hoare_consequence_pre with (P' := (list_reverse_invariant l)).
  eapply hoare_consequence_post.

  Case "list_reverse_program".
    apply hoare_while.
    eapply hoare_consequence_pre.
    eapply hoare_seq.

    SCase "X ::= ATail (AId X)".
      apply hoare_asgn.

    SCase "Y ::= ACons (AHead (AId X)) (AId Y)".
      apply hoare_asgn.

    SCase "{{ exists p, (p ++ X = l /\ rev X ++ Y = rev l) /\ BIsCons X }} => {{ exists p, (p ++ (ATail X) = l /\ rev (ATail X) ++ (ACons (AHead X) Y) = rev l) }}".
      intros.
      inversion H as [Hinv Hb]; clear H.
      inversion Hinv as [p Hinv']; clear Hinv.
      inversion Hinv' as [Hpxl Hrev]; clear Hinv'.
      unfold list_reverse_invariant, assn_sub in *.
      simpl.

      assert (Hxnotnil: bassn (BIsCons (AId X)) st -> aslist (st X) <> nil).
      SSCase "Proof of assertion".
        intros.
        unfold bassn, beval in H.
        simpl in *.
        destruct (aslist (st X)).

        inversion H.

        unfold not.
        intros.
        inversion H0.

      exists (p ++ [head (aslist (st X))]).
      rewrite update_neq.
      split.

      rewrite <- app_assoc.
      simpl.
      rewrite head_tail.
      assumption.
      apply Hxnotnil.
      assumption.

      rewrite <- rev_equation.
      rewrite head_tail.
      assumption.
      apply Hxnotnil.
      assumption.

      reflexivity.

  Case "{{ (exists p, (p ++ X = l /\ rev X ++ Y = rev l)) /\ ~ BIsCons (AId X) }} => {{ Y = rev l }}".
    intros.
    inversion H as [Hinv Hnotb]; clear H.
    inversion Hinv as [p Hinv']; clear Hinv.
    inversion Hinv' as [Hpxl Hrev].
    unfold bassn, beval in *.
    simpl in *.
    remember (aslist (st X)) as Xlist.
    destruct Xlist.

    assumption.

    apply ex_falso_quodlibet.
    apply Hnotb.
    reflexivity.

  Case "{{ X = l ∧ Y = nil }} => {{ exists p, (p ++ X = l /\ rev X ++ Y = rev l) }}".
    intros.
    inversion H as [Hx Hy]; clear H.
    unfold list_reverse_invariant.
    exists [ ].
    split.

    assumption.

    rewrite Hx.
    rewrite Hy.
    rewrite append_nil.
    reflexivity.
Qed.


(********************************
  修飾付きプログラムの形式化
*********************************)

(* -----
  構文
-------- *)

Inductive dcom : Type :=
  | DCSkip : Assertion -> dcom
  | DCSeq : dcom -> dcom -> dcom
  | DCAsgn : id -> aexp -> Assertion -> dcom
  | DCIf : bexp -> Assertion -> dcom -> Assertion -> dcom -> dcom
  | DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
  | DCPre : Assertion -> dcom -> dcom
  | DCPost : dcom -> Assertion -> dcom.

Tactic Notation "dcom_cases" tactic(first) ident(c) :=
  first;
  [
      Case_aux c "Skip"
    | Case_aux c "Seq"
    | Case_aux c "Asgn"
    | Case_aux c "If"
    | Case_aux c "While"
    | Case_aux c "Pre"
    | Case_aux c "Post"
  ].

Notation "'SKIP' {{ P }}" :=
      (DCSkip P)
      (at level 10) : dcom_scope.
Notation "l '::=' a {{ P }}" :=
      (DCAsgn l a P)
      (at level 60, a at next level) : dcom_scope.
Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}" :=
      (DCWhile b Pbody d Ppost)
      (at level 80, right associativity) : dcom_scope.
Notation "'IFB' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI'" :=
      (DCIf b P d P' d')
      (at level 80, right associativity) : dcom_scope.
Notation "'=>' {{ P }} d" :=
      (DCPre P d)
      (at level 90, right associativity) : dcom_scope.
Notation "{{ P }} d" :=
      (DCPre P d)
      (at level 90) : dcom_scope.
Notation "d '=>' {{ P }}" :=
      (DCPost d P)
      (at level 91, right associativity) : dcom_scope.
Notation " d ; d' " :=
      (DCSeq d d')
      (at level 80, right associativity) : dcom_scope.

Delimit Scope dcom_scope with dcom.

Example dec_while : dcom := (
  {{ fun st => True }}
  WHILE
    (BNot (BEq (AId X) (ANum 0)))
  DO
    {{ fun st => ~(asnat (st X) = 0) }}
    X ::= (AMinus (AId X) (ANum 1))
    {{ fun _ => True }}
  END
  {{ fun st => asnat (st X) = 0 }}
) % dcom.

Fixpoint extract (d : dcom) : com :=
  match d with
  | DCSkip _ => SKIP
  | DCSeq d1 d2 => (extract d1 ; extract d2)
  | DCAsgn V a _ => V ::= a
  | DCIf b _ d1 _ d2 => IFB b THEN extract d1 ELSE extract d2 FI
  | DCWhile b _ d _ => WHILE b DO extract d END
  | DCPre _ d => extract d
  | DCPost d _ => extract d
  end.

Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip P => P
  | DCSeq d1 d2 => post d2
  | DCAsgn V a Q => Q
  | DCIf _ _ d1 _ d2 => post d1
  | DCWhile b Pbody c Ppost => Ppost
  | DCPre _ d => post d
  | DCPost c Q => Q
  end.

Fixpoint pre (d : dcom) : Assertion :=
  match d with
  | DCSkip P => fun st => True
  | DCSeq c1 c2 => pre c1
  | DCAsgn V a Q => fun st => True
  | DCIf _ _ t _ e => fun st => True
  | DCWhile b Pbody c Ppost => fun st => True
  | DCPre P c => P
  | DCPost c Q => pre c
  end.

Definition dec_correct (d : dcom) :=
  {{pre d}} (extract d) {{post d}}.

(* -----
  検証条件の抽出
-------- *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ~~> Q" := (assert_implies P Q) (at level 80).
Notation "P <~~> Q" := (P ~~> Q /\ Q ~~> P) (at level 80).

Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSkip Q =>
      (P ~~> Q)
  | DCSeq d1 d2 =>
      verification_conditions P d1 /\
      verification_conditions (post d1) d2
  | DCAsgn V a Q =>
      (P ~~> assn_sub V a Q)
  | DCIf b P1 t P2 e =>
      ((fun st => P st /\ bassn b st) ~~> P1) /\
      ((fun st => P st /\ ~ (bassn b st)) ~~> P2) /\
      (post t = post e) /\
      verification_conditions P1 t /\
      verification_conditions P2 e
  | DCWhile b Pbody d Ppost =>
      (P ~~> post d) /\
      ((fun st => post d st /\ bassn b st) <~~> Pbody) /\
      ((fun st => post d st /\ ~(bassn b st)) <~~> Ppost) /\
      verification_conditions (fun st => post d st /\ bassn b st) d
  | DCPre P' d =>
      (P ~~> P') /\ verification_conditions P' d
  | DCPost d Q =>
      verification_conditions P d /\ (post d ~~> Q)
  end.

Theorem verification_correct:
  forall d P,
  verification_conditions P d -> {{P}} (extract d) {{post d}}.
Proof.
  dcom_cases (induction d) Case; intros P H; simpl in *.
  Case "Skip".
    eapply hoare_consequence_pre.
      apply hoare_skip.
      assumption.
  Case "Seq".
    inversion H as [H1 H2]. clear H.
    eapply hoare_seq.
      apply IHd2. apply H2.
      apply IHd1. apply H1.
  Case "Asgn".
    eapply hoare_consequence_pre.
      apply hoare_asgn.
      assumption.
  Case "If".
    inversion H as [HPre1 [HPre2 [HQeq [HThen HElse]]]]; clear H.
    apply hoare_if.
      eapply hoare_consequence_pre. apply IHd1. apply HThen. assumption.
      simpl. rewrite HQeq.
      eapply hoare_consequence_pre. apply IHd2. apply HElse. assumption.
  Case "While".
    rename a into Pbody. rename a0 into Ppost.
    inversion H as [Hpre [Hbody [Hpost Hd]]]; clear H.
    eapply hoare_consequence.
    apply hoare_while with (P := post d).
      apply IHd. apply Hd.
      assumption. apply Hpost.
  Case "Pre".
    inversion H as [HP Hd]; clear H.
    eapply hoare_consequence_pre. apply IHd. apply Hd. assumption.
  Case "Post".
    inversion H as [Hd HQ]; clear H.
    eapply hoare_consequence_post. apply IHd. apply Hd. assumption.
Qed.

(* -----
  例
-------- *)

Eval simpl in (verification_conditions (fun st => True) dec_while).

Tactic Notation "verify" :=
  try apply verification_correct;
  repeat split;
  simpl; unfold assert_implies;
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; simpl in *;
  intros;
  repeat match goal with [H : _ /\ _ |- _] => destruct H end;
  try eauto; try lia.

Theorem dec_while_correct :
  dec_correct dec_while.
Proof.
  verify; destruct (asnat (st X)).
    inversion H0.
    unfold not. intros. inversion H1.
    apply ex_falso_quodlibet. apply H. reflexivity.
    reflexivity.
    reflexivity.
    apply ex_falso_quodlibet. apply H0. reflexivity.
    unfold not. intros. inversion H0.
    inversion H.
Qed.

Example subtract_slowly_dec (x : nat) (z : nat) : dcom := (
  {{ fun st => asnat (st X) = x /\ asnat (st Z) = z }}
  WHILE
    BNot (BEq (AId X) (ANum 0))
  DO
    {{
      fun st => asnat (st Z) - asnat (st X) = z - x /\
      bassn (BNot (BEq (AId X) (ANum 0))) st
    }}
    Z ::= AMinus (AId Z) (ANum 1)
    {{ fun st => asnat (st Z) - (asnat (st X) - 1) = z - x }} ;
    X ::= AMinus (AId X) (ANum 1)
    {{ fun st => asnat (st Z) - asnat (st X) = z - x }}
  END
  {{
    fun st =>
      asnat (st Z) - asnat (st X) = z - x /\
      ~ bassn (BNot (BEq (AId X) (ANum 0))) st
  }}
  =>
  {{
    fun st =>
      asnat (st Z) = z - x
  }}
) % dcom.

Theorem subtract_slowly_dec_correct:
  forall x z,
  dec_correct (subtract_slowly_dec x z).
Proof.
  intros. verify.
    rewrite <- H.
    assert (H1: update st Z (VNat (asnat (st Z) - 1)) X = st X).
      apply update_neq. reflexivity.
    rewrite -> H1. destruct (asnat (st X)) as [| X'].
      inversion H0. simpl. rewrite Nat.sub_0_r. lia.
    destruct (asnat (st X)).
      lia.
      apply ex_falso_quodlibet. apply H0. reflexivity.
Qed.

(* 練習問題: ★★★ (slow_assignment_dec) *)
Example slow_assignment_dec (x : nat) : dcom := (
  {{ fun st => True }}
  X ::= (ANum x)
  {{ fun st => asnat (st X) = x }} ;
  Y ::= (ANum 0)
  {{ fun st => asnat (st X) = x /\ asnat (st Y) = 0 }} ;
  WHILE
    BNot (BEq (AId X) (ANum 0))
  DO
    {{ fun st => asnat (st X) + asnat (st Y) = x /\ asnat (st X) > 0 }}
    X ::= AMinus (AId X) (ANum 1)
    {{ fun st => asnat (st Y) + asnat (st X) + 1 = x }} ;
    Y ::= APlus (AId Y) (ANum 1)
    {{ fun st => asnat (st Y) + asnat (st X) = x }}
  END
  {{ fun st => asnat (st Y) = x /\ asnat (st X) = 0 }}
) % dcom.

Theorem slow_assignment_correct:
  forall x,
  dec_correct (slow_assignment_dec x).
Proof.
  intros.
  verify.

    destruct (asnat (st X)).
    inversion H0.
    lia.

    destruct (asnat (st X)).
    inversion H0.
    reflexivity.

    destruct (asnat (st X)).
    lia.
    apply ex_falso_quodlibet.
    apply H0.
    reflexivity.

    destruct (asnat (st X)).
    reflexivity.
    apply ex_falso_quodlibet.
    apply H0.
    reflexivity.

    rewrite H0.
    simpl.
    unfold not.
    intros.
    inversion H1.

    destruct (asnat (st X)).
    inversion H0.
    rewrite update_neq.
    lia.
    reflexivity.

    rewrite update_neq.
    lia.
    reflexivity.
Qed.


(* 練習問題: ★★★★, optional (factorial_dec) *)
Fixpoint real_fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

Example fact_dec (x : nat) : dcom := (
  {{ fun st => asnat (st X) = x }} =>
  {{ fun st => asnat (st X) = x /\ asnat (st X) = asnat (st X) /\ 1 = 1 }}
  Z ::= (AId X)
  {{ fun st => asnat (st X) = x /\ asnat (st Z) = asnat (st X) /\ 1 = 1 }};
  Y ::= (ANum 1)
  {{ fun st => asnat (st X) = x /\ asnat (st Z) = asnat (st X) /\ asnat (st Y) = 1 }}; =>
  {{ fun st => asnat (st Y) * real_fact (asnat (st Z)) = real_fact x }}
  WHILE
    BNot (BEq (AId Z) (ANum 0))
  DO
    {{ fun st => asnat (st Y) * real_fact (asnat (st Z)) = real_fact x /\ asnat (st Z) <> 0 }} =>
    {{ fun st => (asnat (st Y) * asnat (st Z)) * real_fact (asnat (st Z) - 1) = real_fact x }}
    Y ::= AMult (AId Y) (AId Z)
    {{ fun st => asnat (st Y) * real_fact (asnat (st Z) - 1) = real_fact x }};
    Z ::= AMinus (AId Z) (ANum 1)
    {{ fun st => asnat (st Y) * real_fact (asnat (st Z)) = real_fact x }}
  END
  {{ fun st => asnat (st Y) * real_fact (asnat (st Z)) = real_fact x /\ ~ (asnat (st Z) <> 0) }} =>
  {{ fun st => asnat (st Y) = real_fact x }} 
) % dcom.

Lemma real_fact_pre :
  forall n,
  n <> 0 ->
  n * real_fact (n - 1) = real_fact n.
Proof.
  intros.
  destruct n.

  Case "n = 0".
    apply ex_falso_quodlibet.
    apply H.
    reflexivity.

  Case "n <> 0".
    simpl.
    rewrite Nat.sub_0_r.
    reflexivity.
Qed.

Theorem fact_correct:
  forall x,
  dec_correct (fact_dec x).
Proof.
  intros.
  verify.

    rewrite H1.
    rewrite H0.
    rewrite H.
    lia.

    destruct (asnat (st Z)).
    inversion H0.
    unfold not.
    intros.
    inversion H1.

    destruct (asnat (st Z)).
    lia.
    reflexivity.

    unfold not.
    intros.
    destruct (asnat (st Z)).
    apply H1.
    reflexivity.
    apply H0.
    reflexivity.

    unfold not.
    intros.
    destruct (asnat (st Z)).
    inversion H1.
    apply H0.
    auto.

    apply Bool.negb_true_iff in H0.
    apply Nat.eqb_neq in H0.
    rewrite <- Nat.mul_assoc.
    rewrite (real_fact_pre (asnat (st Z)) H0).
    assumption.

    destruct (asnat (st Z)).
    simpl in H.
    lia.
    unfold not in H0.
    apply ex_falso_quodlibet.
    apply H0.
    intros.
    inversion H1.
Qed.

Definition list_member_dec (n : nat) (l : list nat) : dcom := (
  {{ fun st => st X = VList l /\ st Y = VNat n /\ st Z = VNat 0 }}
  WHILE
    BIsCons (AId X)
  DO
    {{
      fun st =>
        st Y = VNat n /\
        (
          exists p,
            p ++ aslist (st X) = l /\
            (st Z = VNat 1 <-> appears_in n p)
        ) /\
        bassn (BIsCons (AId X)) st
    }}
    IFB
      (BEq (AId Y) (AHead (AId X)))
    THEN
      {{
        fun st =>
          (
            (
              st Y = VNat n /\
              (
                exists p,
                p ++ aslist (st X) = l /\
                (st Z = VNat 1 <-> appears_in n p)
              )
            ) /\
            bassn (BIsCons (AId X)) st
          ) /\
          bassn (BEq (AId Y) (AHead (AId X))) st
      }}
      =>
      {{
        fun st =>
          st Y = VNat n /\
          (
            exists p,
            p ++ tail (aslist (st X)) = l /\
            (VNat 1 = VNat 1 <-> appears_in n p)
          )
      }}
      Z ::= ANum 1
      {{
        fun st =>
          st Y = VNat n /\
          (
            exists p,
            p ++ tail (aslist (st X)) = l /\
            (st Z = VNat 1 <-> appears_in n p)
          )
      }}
    ELSE
      {{
        fun st =>
          (
            (
              st Y = VNat n /\
              (
                exists p,
                p ++ aslist (st X) = l /\
                (st Z = VNat 1 <-> appears_in n p)
              )
            ) /\
            bassn (BIsCons (AId X)) st
          ) /\
          ~bassn (BEq (AId Y) (AHead (AId X))) st
      }}
      =>
      {{
        fun st =>
          st Y = VNat n /\
          (
            exists p,
            p ++ tail (aslist (st X)) = l /\
            (st Z = VNat 1 <-> appears_in n p)
          )
      }}
      SKIP
      {{
        fun st =>
          st Y = VNat n /\
          (
            exists p,
            p ++ tail (aslist (st X)) = l /\
            (st Z = VNat 1 <-> appears_in n p)
          )
      }}
    FI ;
    X ::= (ATail (AId X))
    {{
      fun st =>
        st Y = VNat n /\
        (
          exists p : list nat,
          p ++ aslist (st X) = l /\
          (st Z = VNat 1 <-> appears_in n p)
        )
    }}
  END
  {{
    fun st =>
      (
        st Y = VNat n /\
        (
          exists p,
          p ++ aslist (st X) = l /\
          (st Z = VNat 1 <-> appears_in n p)
        )
      ) /\
      ~ bassn (BIsCons (AId X)) st
  }}
  =>
  {{ fun st => st Z = VNat 1 <-> appears_in n l }}
) %dcom.

Theorem list_member_correct':
  forall n l,
  dec_correct (list_member_dec n l).
Proof.
  intros n l.
  verify.
  Case "The loop precondition holds.".
    exists []. simpl. split.
      rewrite H. reflexivity.
      rewrite H1. split; inversion 1.
  Case "IF taken".
    destruct H2 as [p [H3 H4]].
    remember (aslist (st X)) as x.
    destruct x as [|h x'].
      inversion H1.
      exists (snoc p h).
      simpl. split.
         rewrite snoc_equation. assumption.
         split.
           rewrite H in H0.
           simpl in H0.
           rewrite (beq_true__eq _ _ H0).
           intros. apply appears_in_snoc1.
           intros. reflexivity.
  Case "If not taken".
    destruct H2 as [p [H3 H4]].
    remember (aslist (st X)) as x.
    destruct x as [|h x'].
      inversion H1.
      exists (snoc p h).
      split.
        rewrite snoc_equation. assumption.
        split.
          intros. apply appears_in_snoc2. apply H4. assumption.
          intros Hai. destruct (appears_in_snoc3 _ _ _ Hai).
          SCase "later". apply H4. assumption.
          SCase "here (absurd)".
            subst.
            simpl in H0. rewrite H in H0. rewrite beq_nat_refl in H0.
            apply ex_falso_quodlibet. apply H0. reflexivity.
  Case "Loop postcondition implies desired conclusion (->)".
    destruct H2 as [p [H3 H4]].
    unfold bassn in H1. simpl in H1.
    destruct (aslist (st X)) as [|h x'].
       rewrite append_nil in H3. subst. apply H4. assumption.
       apply ex_falso_quodlibet. apply H1. reflexivity.
  Case "loop postcondition implies desired conclusion (<-)".
    destruct H2 as [p [H3 H4]].
    unfold bassn in H1. simpl in H1.
    destruct (aslist (st X)) as [|h x'].
       rewrite append_nil in H3. subst. apply H4. assumption.
       apply ex_falso_quodlibet. apply H1. reflexivity.
Qed.
