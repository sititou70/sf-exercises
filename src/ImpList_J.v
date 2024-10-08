Require Import Unicode.Utf8.
Require Import commons.
Require Import Arith.
Require Import Lia.

(********************************
  リストを持つ Imp プログラム
*********************************)

(* -----
  定義の繰り返し
-------- *)

Inductive id : Type :=
  Id : nat -> id.

Definition beq_id id1 id2 :=
  match (id1, id2) with
    (Id n1, Id n2) => Nat.eqb n1 n2
  end.

Theorem beq_id_refl :
  forall i,
  true = beq_id i i.
Proof.
  intros.
  destruct i.
  unfold beq_id.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem beq_id_eq :
  forall i1 i2,
  true = beq_id i1 i2 ->
  i1 = i2.
Proof.
  intros i1 i2 H.
  destruct i1.
  destruct i2.
  specialize (eq_sym H) as Hsym.
  apply (Nat.eqb_eq n n0) in Hsym.
  subst.
  reflexivity.
Qed.

Theorem beq_id_false_not_eq :
  forall i1 i2,
  beq_id i1 i2 = false ->
  i1 <> i2.
Proof.
  unfold not.
  intros.
  destruct i1.
  destruct i2.
  inversion H0.
  unfold beq_id in H.
  apply Nat.eqb_neq in H.
  unfold not in H.
  apply H in H2.
  assumption.
Qed.

Theorem not_eq_beq_id_false :
  forall i1 i2,
  i1 <> i2 ->
  beq_id i1 i2 = false.
Proof.
  unfold not.
  intros.
  destruct i1.
  destruct i2.
  unfold beq_id.
  apply Nat.eqb_neq.
  unfold not.
  intros.
  subst.
  apply H.
  reflexivity.
Qed.

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

(* -----
  拡張
-------- *)
Inductive val : Type :=
  | VNat : nat -> val
  | VList : list nat -> val.

Definition state := id -> val.

Definition empty_state : state := fun _ => VNat 0.
Definition update (st : state) (V : id) (n : val) : state :=
  fun V' => if beq_id V V' then n else st V'.

Definition asnat (v : val) : nat :=
  match v with
  | VNat n => n
  | VList _ => 0
  end.

Definition aslist (v : val) : list nat :=
  match v with
  | VNat n => []
  | VList xs => xs
  end.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | AHead : aexp -> aexp
  | ATail : aexp -> aexp
  | ACons : aexp -> aexp -> aexp
  | ANil : aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [
      Case_aux c "ANum"
    | Case_aux c "AId"
    | Case_aux c "APlus"
    | Case_aux c "AMinus"
    | Case_aux c "AMult"
    | Case_aux c "AHead"
    | Case_aux c "ATail"
    | Case_aux c "ACons"
    | Case_aux c "ANil"
  ].

Definition tail (l : list nat) :=
  match l with
  | x :: xs => xs
  | [] => []
  end.

Definition head (l : list nat) :=
  match l with
  | x :: xs => x
  | [] => 0
  end.

Fixpoint aeval (st : state) (e : aexp) : val :=
  match e with
  | ANum n => VNat n
  | AId i => st i
  | APlus a1 a2 => VNat (asnat (aeval st a1) + asnat (aeval st a2))
  | AMinus a1 a2 => VNat (asnat (aeval st a1) - asnat (aeval st a2))
  | AMult a1 a2 => VNat (asnat (aeval st a1) * asnat (aeval st a2))
  | ATail a => VList (tail (aslist (aeval st a)))
  | AHead a => VNat (head (aslist (aeval st a)))
  | ACons a1 a2 => VList (asnat (aeval st a1) :: aslist (aeval st a2))
  | ANil => VList []
  end.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp
  | BIsCons : aexp -> bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [
      Case_aux c "BTrue"
    | Case_aux c "BFalse"
    | Case_aux c "BEq"
    | Case_aux c "BLe"
    | Case_aux c "BNot"
    | Case_aux c "BAnd"
    | Case_aux c "BIsCons"
  ].

Fixpoint beval (st : state) (e : bexp) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => Nat.eqb (asnat (aeval st a1)) (asnat (aeval st a2))
  | BLe a1 a2 => Nat.leb (asnat (aeval st a1)) (asnat (aeval st a2))
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  | BIsCons a => match aslist (aeval st a) with
                  | _::_ => true
                  | [] => false
                 end
  end.

(* -----
  定義の繰り返し
-------- *)

Theorem update_eq :
  forall n V st,
  (update st V n) V = n.
Proof.
  intros n V st.
  unfold update.
  rewrite <- beq_id_refl.
  reflexivity.
Qed.

Theorem update_neq :
  forall V2 V1 n st,
  beq_id V2 V1 = false ->
  (update st V2 n) V1 = (st V1).
Proof.
  intros V2 V1 n st Hneq.
  unfold update.
  rewrite -> Hneq.
  reflexivity.
Qed.

Theorem update_shadow :
  forall x1 x2 k1 k2 (f : state),
  (update (update f k2 x1) k2 x2) k1 = (update f k2 x2) k1.
Proof.
  intros x1 x2 k1 k2 f.
  unfold update.
  destruct (beq_id k2 k1); reflexivity.
Qed.

Theorem update_same :
  forall x1 k1 k2 (f : state),
  f k1 = x1 ->
  (update f k1 x1) k2 = f k2.
Proof.
  intros x1 k1 k2 f Heq.
  unfold update. subst.
  remember (beq_id k1 k2) as b.
  destruct b.
  Case "true".
    apply beq_id_eq in Heqb. subst. reflexivity.
  Case "false".
    reflexivity.
Qed.

Theorem update_permute :
  forall x1 x2 k1 k2 k3 f,
  beq_id k2 k1 = false ->
  (update (update f k2 x1) k1 x2) k3 = (update (update f k1 x2) k2 x1) k3.
Proof.
  intros x1 x2 k1 k2 k3 f H.
  unfold update.
  remember (beq_id k1 k3) as b13.
  remember (beq_id k2 k3) as b23.
  apply beq_id_false_not_eq in H.
  destruct b13; try reflexivity.
  Case "true".
    destruct b23; try reflexivity.
    SCase "true".
      apply beq_id_eq in Heqb13.
      apply beq_id_eq in Heqb23.
      subst. assert (k3 = k3) by reflexivity. apply H in H0. inversion H0.
Qed.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [
      Case_aux c "SKIP"
    | Case_aux c "::="
    | Case_aux c ";"
    | Case_aux c "IFB"
    | Case_aux c "WHILE"
  ].

Notation "'SKIP'" :=
  CSkip.
Notation "l '::=' a" :=
  (CAss l a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).
Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip :
    forall st,
      SKIP / st || st
  | E_Asgn :
    forall st a1 n l,
      aeval st a1 = n ->
      (l ::= a1) / st || (update st l n)
  | E_Seq :
    forall c1 c2 st st' st'',
      c1 / st || st' ->
      c2 / st' || st'' ->
      (c1 ; c2) / st || st''
  | E_IfTrue :
    forall st st' b1 c1 c2,
      beval st b1 = true ->
      c1 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse :
    forall st st' b1 c1 c2,
      beval st b1 = false ->
      c2 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd :
    forall b1 st c1,
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop :
    forall st st' st'' b1 c1,
      beval st b1 = true ->
      c1 / st || st' ->
      (WHILE b1 DO c1 END) / st' || st'' ->
      (WHILE b1 DO c1 END) / st || st''
  where "c1 '/' st '||' st'" := (ceval st c1 st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [
      Case_aux c "E_Skip"
    | Case_aux c "E_Asgn"
    | Case_aux c "E_Seq"
    | Case_aux c "E_IfTrue"
    | Case_aux c "E_IfFalse"
    | Case_aux c "E_WhileEnd"
    | Case_aux c "E_WhileLoop"
].

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

Theorem loop_never_stops :
  forall st st',
  ~(loop / st || st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef.
  ceval_cases (induction contra) Case; try (inversion Heqloopdef).
    Case "E_WhileEnd".
      rewrite -> H1 in H. inversion H.
    Case "E_WhileLoop".
      apply IHcontra2. subst. reflexivity.
Qed.
