Require Import Unicode.Utf8.
Require Import commons.
Require Import Arith.
Require Import Lia.

(********************************
  算術式とブール式
*********************************)

Module AExp.
  (* -----
    構文
  -------- *)
  Inductive aexp : Type :=
    | ANum : nat → aexp
    | APlus : aexp → aexp → aexp
    | AMinus : aexp → aexp → aexp
    | AMult : aexp → aexp → aexp.

  Inductive bexp : Type :=
    | BTrue : bexp
    | BFalse : bexp
    | BEq : aexp → aexp → bexp
    | BLe : aexp → aexp → bexp
    | BNot : bexp → bexp
    | BAnd : bexp → bexp → bexp.

  (* -----
    評価
  -------- *)
  Fixpoint aeval (e : aexp) : nat :=
    match e with
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    | AMinus a1 a2 => (aeval a1) - (aeval a2)
    | AMult a1 a2 => (aeval a1) * (aeval a2)
    end.

  Example test_aeval1:
    aeval (APlus (ANum 2) (ANum 2)) = 4.
  Proof. reflexivity. Qed.

  Fixpoint beval (e : bexp) : bool :=
    match e with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => Nat.eqb (aeval a1) (aeval a2)
    | BLe a1 a2 => leb (aeval a1) (aeval a2)
    | BNot b1 => negb (beval b1)
    | BAnd b1 b2 => andb (beval b1) (beval b2)
    end.

  (* -----
    最適化(Optimization)
  -------- *)
  Fixpoint optimize_0plus (e : aexp) : aexp :=
    match e with
    | ANum n =>
        ANum n
    | APlus (ANum 0) e2 =>
        optimize_0plus e2
    | APlus e1 e2 =>
        APlus (optimize_0plus e1) (optimize_0plus e2)
    | AMinus e1 e2 =>
        AMinus (optimize_0plus e1) (optimize_0plus e2)
    | AMult e1 e2 =>
        AMult (optimize_0plus e1) (optimize_0plus e2)
    end.

  Example test_optimize_0plus:
    optimize_0plus (APlus (ANum 2)
                          (APlus (ANum 0)
                                 (APlus (ANum 0) (ANum 1))))
    = APlus (ANum 2) (ANum 1).
  Proof. reflexivity. Qed.

  Theorem optimize_0plus_sound:
    forall e,
    aeval (optimize_0plus e) = aeval e.
  Proof.
    intros e.
    induction e.

      Case "ANum".
      reflexivity.
      
      Case "APlus".
      destruct e1.

        SCase "e1 = ANum n".
        destruct n.
          
          SSCase "n = 0".
          simpl. apply IHe2.
          
          SSCase "n <> 0".
          simpl. rewrite IHe2. reflexivity.

        SCase "e1 = APlus e1_1 e1_2".
        simpl. simpl in IHe1. rewrite IHe1.
        rewrite IHe2. reflexivity.

        SCase "e1 = AMinus e1_1 e1_2".
        simpl. simpl in IHe1. rewrite IHe1.
        rewrite IHe2. reflexivity.

        SCase "e1 = AMult e1_1 e1_2".
        simpl. simpl in IHe1. rewrite IHe1.
        rewrite IHe2. reflexivity.

      Case "AMinus".
      simpl. rewrite IHe1. rewrite IHe2. reflexivity.

      Case "AMult".
      simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  Qed.

  (********************************
    算術式とブール式
  *********************************)

  (* -----
    タクティカル(Tacticals)
  -------- *)
  (* tryタクティカル *)
  (* ;タクティカル *)
  Lemma foo :
    forall n,
    leb 0 n = true.
  Proof.
    intros.
    destruct n.
      Case "n=0". simpl. reflexivity.
      Case "n=Sn'". simpl. reflexivity.
  Qed.

  Lemma foo' :
    forall n,
    leb 0 n = true.
  Proof.
    intros.
    destruct n;
    simpl;
    reflexivity.
  Qed.

  Theorem optimize_0plus_sound':
    forall e,
    aeval (optimize_0plus e) = aeval e.
  Proof.
    intros e.
    induction e;
      try (
        simpl;
        rewrite IHe1;
        rewrite IHe2;
        reflexivity
      ).
    
      Case "ANum". reflexivity.

      Case "APlus".
      destruct e1;
        try (
          simpl;
          simpl in IHe1;
          rewrite IHe1;
          rewrite IHe2;
          reflexivity
        ).

        SCase "e1 = ANum n".
        destruct n; simpl; rewrite IHe2; reflexivity.
  Qed.

  Theorem optimize_0plus_sound'':
    forall e,
    aeval (optimize_0plus e) = aeval e.
  Proof.
    intros e.
    induction e;
      try (
        simpl;
        rewrite IHe1;
        rewrite IHe2;
        reflexivity
      );
      try reflexivity.

      Case "APlus".
      destruct e1;
        try (
          simpl;
          simpl in IHe1;
          rewrite IHe1;
          rewrite IHe2;
          reflexivity
        ).

        SCase "e1 = ANum n".
        destruct n; simpl; rewrite IHe2; reflexivity.
  Qed.

  (* -----
    新しいタクティック記法を定義する
  -------- *)
  Tactic Notation "simpl_and_try" tactic(c) :=
    simpl;
    try c.
  
  (* 場合分けを万全にする *)
  Tactic Notation "aexp_cases" tactic(first) ident(c) :=
    first;
    [
        Case_aux c "ANum"
      | Case_aux c "APlus"
      | Case_aux c "AMinus"
      | Case_aux c "AMult"
    ].

  Theorem optimize_0plus_sound''':
    forall e,
    aeval (optimize_0plus e) = aeval e.
  Proof.
    intros e.
    aexp_cases (induction e) Case;
      try (
        simpl;
        rewrite IHe1;
        rewrite IHe2;
        reflexivity
      );
      try reflexivity.

      Case "APlus".
      aexp_cases (destruct e1) SCase;
        try (
          simpl;
          simpl in IHe1;
          rewrite IHe1;
          rewrite IHe2;
          reflexivity
        ).

        SCase "ANum".
        destruct n; simpl; rewrite IHe2; reflexivity.
  Qed.

  (* 練習問題: ★★★ (optimize_0plus_b) *)
  Fixpoint optimize_0plus_b (e : bexp) : bexp :=
    match e with
    | BTrue =>
        BTrue
    | BFalse =>
        BFalse
    | BEq e1 e2 =>
        BEq (optimize_0plus e1) (optimize_0plus e2)
    | BLe e1 e2 =>
        BLe (optimize_0plus e1) (optimize_0plus e2)
    | BNot e1 =>
        BNot (optimize_0plus_b e1)
    | BAnd e1 e2 =>
        BAnd (optimize_0plus_b e1) (optimize_0plus_b e2)
    end.

  Tactic Notation "bexp_cases" tactic(first) ident(c) :=
    first;
    [
        Case_aux c "BTrue"
      | Case_aux c "BFalse"
      | Case_aux c "BEq"
      | Case_aux c "BLe"
      | Case_aux c "BNot"
      | Case_aux c "BAnd"
    ].

  Theorem optimize_0plus_b_sound:
    forall e,
    beval (optimize_0plus_b e) = beval e.
  Proof.
    intros.
    bexp_cases (induction e) Case;
      try (
        reflexivity
      );
      try (
        simpl;
        rewrite optimize_0plus_sound;
        rewrite optimize_0plus_sound;
        reflexivity
      ).
    
      Case "BNot".
      simpl.
      rewrite IHe.
      reflexivity.

      Case "BAnd".
      simpl.
      rewrite IHe1.
      rewrite IHe2.
      reflexivity.
  Qed.

  (* 練習問題: ★★★★, optional (optimizer) *)
  Fixpoint optimize_TrueAnd (e : bexp) : bexp :=
    match e with
    | BTrue =>
        BTrue
    | BFalse =>
        BFalse
    | BEq e1 e2 =>
        BEq e1 e2
    | BLe e1 e2 =>
        BLe e1 e2
    | BNot e1 =>
        BNot (optimize_TrueAnd e1)
    | BAnd BTrue e2 =>
        e2
    | BAnd e1 e2 =>
        BAnd (optimize_TrueAnd e1) (optimize_TrueAnd e2)
    end.
  
  Theorem optimize_TrueAnd_sound:
    forall e,
    beval (optimize_TrueAnd e) = beval e.
  Proof.
    intros.
    bexp_cases (induction e) Case;
      try (
        reflexivity
      ).
    
      Case "BNot".
      simpl.
      rewrite IHe.
      reflexivity.

      Case "BAnd".
      bexp_cases (destruct e1) SCase;
        try (
          reflexivity
        );
        try (
          simpl;
          try (
            simpl in IHe1;
            rewrite IHe1
          );
          try (
            simpl in IHe2;
            rewrite IHe2
          );
          reflexivity
        ).
  Qed.

  (* -----
    omegaタクティック
  -------- *)
  Example silly_presburger_example :
    forall m n o p,
    m + n <= n + o ∧ o + 3 = p + 3 →
    m <= p.
  Proof.
    intros. lia.
  Qed.

  (********************************
    関係としての評価
  *********************************)
  Module aevalR_first_try.
    Inductive aevalR : aexp → nat → Prop :=
      | E_ANum : forall (n: nat),
          aevalR (ANum n) n
      | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 →
          aevalR e2 n2 →
          aevalR (APlus e1 e2) (n1 + n2)
      | E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 →
          aevalR e2 n2 →
          aevalR (AMinus e1 e2) (n1 - n2)
      | E_AMult : forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 →
          aevalR e2 n2 →
          aevalR (AMult e1 e2) (n1 * n2).
    Notation "e '||' n" := (aevalR e n) : type_scope.
  End aevalR_first_try.

  Reserved Notation "e '||' n" (at level 50, left associativity).
  Inductive aevalR : aexp → nat → Prop :=
    | E_ANum : forall (n:nat),
        (ANum n) || n
    | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
        (e1 || n1) → (e2 || n2) → (APlus e1 e2) || (n1 + n2)
    | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
        (e1 || n1) → (e2 || n2) → (AMinus e1 e2) || (n1 - n2)
    | E_AMult : forall (e1 e2: aexp) (n1 n2 : nat),
        (e1 || n1) → (e2 || n2) → (AMult e1 e2) || (n1 * n2)
    where "e '||' n" := (aevalR e n) : type_scope.

  Tactic Notation "aevalR_cases" tactic(first) ident(c) :=
    first;
    [
        Case_aux c "E_ANum"
      | Case_aux c "E_APlus"
      | Case_aux c "E_AMinus"
      | Case_aux c "E_AMult"
    ].

  Theorem aeval_iff_aevalR :
    forall a n,
    (a || n) <-> aeval a = n.
  Proof.
    split.

    Case "->".
      intros H.
      aevalR_cases (induction H) SCase; simpl.

      SCase "E_ANum".
        reflexivity.

      SCase "E_APlus".
        rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.

      SCase "E_AMinus".
        rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.

      SCase "E_AMult".
        rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.

    Case "<-".
      generalize dependent n.
      aexp_cases (induction a) SCase;
        simpl; intros; subst.

      SCase "ANum".
        apply E_ANum.

      SCase "APlus".
        apply E_APlus.
        apply IHa1. reflexivity.
        apply IHa2. reflexivity.

      SCase "AMinus".
        apply E_AMinus.
        apply IHa1. reflexivity.
        apply IHa2. reflexivity.

      SCase "AMult".
        apply E_AMult.
        apply IHa1. reflexivity.
        apply IHa2. reflexivity.
  Qed.

  Theorem aeval_iff_aevalR' :
    forall a n,
    (a || n) <-> aeval a = n.
  Proof.
    split.
    Case "->".
      intros H; induction H; subst; reflexivity.
    Case "<-".
      generalize dependent n.
      induction a; simpl; intros; subst; constructor;
        try apply IHa1; try apply IHa2; reflexivity.
  Qed.

  (* 練習問題: ★★, optional (bevalR) *)
  Reserved Notation "e '||b' b" (at level 50, left associativity).
  Inductive bevalR : bexp -> bool -> Prop :=
    | E_BTrue :
        BTrue ||b true
    | E_BFalse :
        BFalse ||b false
    | E_BEq : forall (e1 e2 : aexp) (n1 n2 : nat),
        (e1 || n1) ->
        (e2 || n2) ->
        (BEq e1 e2) ||b Nat.eqb n1 n2
    | E_BLe : forall (e1 e2 : aexp) (n1 n2 : nat),
        (e1 || n1) ->
        (e2 || n2) ->
        (BLe e1 e2) ||b Nat.leb n1 n2
    | E_BNot : forall (e1 : bexp) (b1 : bool),
        (e1 ||b b1) ->
        (BNot e1) ||b negb b1
    | E_BAnd : forall (e1 e2 : bexp) (b1 b2 : bool),
        (e1 ||b b1) ->
        (e2 ||b b2) ->
        (BAnd e1 e2) ||b andb b1 b2
    where "e '||b' b" := (bevalR e b) : type_scope.

  Tactic Notation "bevalR_cases" tactic(first) ident(c) :=
    first;
    [
        Case_aux c "E_BTrue"
      | Case_aux c "E_BFalse"
      | Case_aux c "E_BEq"
      | Case_aux c "E_BLe"
      | Case_aux c "E_BNot"
      | Case_aux c "E_BAnd"
    ].

  Theorem beval_iff_bevalR :
    forall e b,
    (e ||b b) <-> beval e = b.
  Proof.
    split.
    Case "->".
      intros.
      bevalR_cases (induction H) SCase;
        try solve [
          simpl;
          subst;
          reflexivity
        ];
        try solve [
          simpl;
          apply aeval_iff_aevalR in H; subst;
          apply aeval_iff_aevalR in H0; subst;
          reflexivity
        ].
    Case "<-".
      generalize dependent b.
      bexp_cases (induction e) SCase;
        try solve [
          intros;
          subst;
          constructor;
          try solve [
            apply aeval_iff_aevalR;
            reflexivity
          ]
        ].

      SCase "BNot".
        intros.
        subst.
        simpl.
        constructor.
        apply IHe.
        reflexivity.
        
      SCase "BAnd".
        intros.
        subst.
        simpl.
        constructor.

          apply IHe1.
          reflexivity.

          apply IHe2.
          reflexivity.
  Qed.
End AExp.

(********************************
  変数を持つ式
*********************************)

(* -----
  識別子
-------- *)

Module Id.
  Inductive id : Type :=
    Id : nat → id.

  Definition beq_id X1 X2 :=
    match (X1, X2) with
      (Id n1, Id n2) => Nat.eqb n1 n2
    end.

  Theorem beq_id_refl :
    forall X,
    true = beq_id X X.
  Proof.
    intros. destruct X.
    unfold beq_id.
    rewrite Nat.eqb_refl.
    reflexivity.
  Qed.

  (* 練習問題: ★, optional (beq_id_eq) *)
  Theorem beq_id_eq :
    forall i1 i2,
    true = beq_id i1 i2 ->
    i1 = i2.
  Proof.
    intros.
    destruct i1.
    destruct i2.
    unfold beq_id in H.
    specialize (eq_sym H) as Hsym.
    apply (Nat.eqb_eq n n0) in Hsym.
    subst.
    reflexivity.
  Qed.

  (* 練習問題: ★, optional (beq_id_false_not_eq) *)
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

  (* 練習問題: ★, optional (not_eq_beq_id_false) *)
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

  (* 練習問題: ★, optional (beq_id_sym) *)
  Theorem beq_id_sym :
    forall i1 i2,
    beq_id i1 i2 = beq_id i2 i1.
  Proof.
    intros.
    destruct i1.
    destruct i2.
    unfold beq_id.
    apply Nat.eqb_sym.
  Qed.
End Id.

(* -----
  状態
-------- *)

Definition state := Id.id → nat.

Definition empty_state : state :=
  fun _ => 0.

Definition update (st : state) (X : Id.id) (n : nat) : state :=
  fun X' => if Id.beq_id X X' then n else st X'.

(* 練習問題: ★★, optional (update_eq) *)
Theorem update_eq :
  forall n X st,
  (update st X n) X = n.
Proof.
  intros.
  unfold update.
  rewrite <- Id.beq_id_refl.
  reflexivity.
Qed.

(* 練習問題: ★★, optional (update_neq) *)
Theorem update_neq : 
  forall V2 V1 n st,
  Id.beq_id V2 V1 = false ->
  (update st V2 n) V1 = (st V1).
Proof.
  intros.
  unfold update.
  rewrite H.
  reflexivity.
Qed.

(* 練習問題: ★★, optional (update_example) *)
Theorem update_example :
  forall (n : nat),
  (update empty_state (Id.Id 2) n) (Id.Id 3) = 0.
Proof.
  intros.
  unfold update.
  simpl.
  unfold empty_state.
  reflexivity.
Qed.

(* 練習問題: ★★ (update_shadow) *)
Theorem update_shadow :
  forall x1 x2 k1 k2 (f : state),
  (update (update f k2 x1) k2 x2) k1 = (update f k2 x2) k1.
Proof.
  intros.
  unfold update.
  destruct k1 as [n1].
  destruct k2 as [n2].
  destruct (dec_eq_nat n1 n2).

  Case "n1 = n2".
    subst.
    rewrite <- Id.beq_id_refl.
    reflexivity.

  Case "n1 <> n2".
    unfold not in H.
    unfold Id.beq_id.
    apply Nat.eqb_neq in H.
    rewrite Nat.eqb_sym in H.
    rewrite H.
    reflexivity.
Qed.

(* 練習問題: ★★, optional (update_same) *)
Theorem update_same :
  forall x1 k1 k2 (f : state),
  f k1 = x1 ->
  (update f k1 x1) k2 = f k2.
Proof.
  intros.
  unfold update.
  destruct k1 as [n1].
  destruct k2 as [n2].
  destruct (dec_eq_nat n1 n2).

  Case "n1 = n2".
    subst.
    rewrite <- Id.beq_id_refl.
    reflexivity.

  Case "n1 <> n2".
    unfold not in H0.
    unfold Id.beq_id.
    apply Nat.eqb_neq in H0.
    rewrite H0.
    reflexivity.
Qed.

(* 練習問題: ★★, optional (update_permute) *)
Theorem update_permute :
  forall x1 x2 k1 k2 k3 f,
  Id.beq_id k2 k1 = false ->
  (update (update f k2 x1) k1 x2) k3 = (update (update f k1 x2) k2 x1) k3.
Proof.
  intros.
  unfold update.
  destruct k1 as [n1].
  destruct k2 as [n2].
  destruct k3 as [n3].
  destruct (dec_eq_nat n3 n1).

  Case "n3 = n1".
    destruct (dec_eq_nat n3 n2).

    SCase "n3 = n2".
      subst.
      rewrite <- Id.beq_id_refl in H.
      inversion H.

    SCase "n3 <> n2".
      subst.
      rewrite <- Id.beq_id_refl.
      rewrite H.
      reflexivity.

  Case "n3 <> n1".
    destruct (dec_eq_nat n3 n2).

    SCase "n3 = n2".
      subst.
      rewrite <- Id.beq_id_refl.
      rewrite Id.beq_id_sym in H.
      rewrite H.
      reflexivity.

    SCase "n3 <> n2".
      unfold Id.beq_id.
      apply Nat.eqb_neq in H0.
      apply Nat.eqb_neq in H1.
      rewrite Nat.eqb_sym in H0.
      rewrite Nat.eqb_sym in H1.
      rewrite H0.
      rewrite H1.
      reflexivity.
Qed.

(* -----
  構文
-------- *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : Id.id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [
      Case_aux c "ANum"
    | Case_aux c "AId"
    | Case_aux c "APlus"
    | Case_aux c "AMinus"
    | Case_aux c "AMult"
  ].

Definition X : Id.id := Id.Id 0.
Definition Y : Id.id := Id.Id 1.
Definition Z : Id.id := Id.Id 2.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp → aexp → bexp
  | BLe : aexp → aexp → bexp
  | BNot : bexp → bexp
  | BAnd : bexp → bexp → bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [
      Case_aux c "BTrue"
    | Case_aux c "BFalse"
    | Case_aux c "BEq"
    | Case_aux c "BLe"
    | Case_aux c "BNot"
    | Case_aux c "BAnd"
  ].

(* -----
  評価
-------- *)

Fixpoint aeval (st : state) (e : aexp) : nat :=
  match e with
  | ANum n => n
  | AId X => st X
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (e : bexp) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => Nat.eqb (aeval st a1) (aeval st a2)
  | BLe a1 a2 => Nat.leb (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Example aexp1 :
  aeval
    (update empty_state X 5)
    (APlus (ANum 3) (AMult (AId X) (ANum 2)))
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
  beval
    (update empty_state X 5)
    (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
  = true.
Proof. reflexivity. Qed.

(********************************
  コマンド
*********************************)

Inductive com : Type :=
  | CSkip : com
  | CAss : Id.id -> aexp -> com
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
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;
  X ::= AMinus (AId X) (ANum 1).

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;
  Z ::= ANum 5 ;
  subtract_slowly.

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

Definition fact_body : com :=
  Y ::= AMult (AId Y) (AId Z) ;
  Z ::= AMinus (AId Z) (ANum 1).

Definition fact_loop : com :=
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    fact_body
  END.

Definition fact_com : com :=
  Z ::= AId X ;
  Y ::= ANum 1 ;
  fact_loop.

(********************************
  評価
*********************************)

(* -----
  評価関数
-------- *)
Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
    | SKIP =>
        st
    | l ::= a1 =>
        update st l (aeval st a1)
    | c1 ; c2 =>
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_step1 st c1
          else ceval_step1 st c2
    | WHILE b1 DO c1 END =>
        st
  end.

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => empty_state
  | S i' =>
    match c with
      | SKIP =>
          st
      | l ::= a1 =>
          update st l (aeval st a1)
      | c1 ; c2 =>
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step2 st c1 i'
            else ceval_step2 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.

Fixpoint ceval_step3 (st : state) (c : com) (i : nat) : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (update st l (aeval st a1))
      | c1 ; c2 =>
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step3 st c1 i'
            else ceval_step3 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat) : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (update st l (aeval st a1))
      | c1 ; c2 =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.

Definition test_ceval (st : state) (c : com) :=
  match ceval_step st c 500 with
  | None => None
  | Some st => Some (st X, st Y, st Z)
  end.

(* 練習問題: ★★, recommended (pup_to_n) *)
Definition pup_to_n : com :=
  Y ::= ANum 0 ;
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    Y ::= APlus (AId Y) (AId X) ;
    X ::= AMinus (AId X) (ANum 1)
  END.

Example pup_to_n_test :
  test_ceval
    (update empty_state X 10)
    pup_to_n
  = Some (0, 55, 0).
Proof.
  compute.
  reflexivity.
Qed.

(* 練習問題: ★★, optional (peven) *)
Definition peven : com :=
  Z ::= AId X ;
  WHILE
    BNot (BLe (AId Z) (ANum 1))
  DO
    Z ::= AMinus (AId Z) (ANum 2)
  END.

Example peven_test1 : test_ceval (update empty_state X 10) peven = Some (10, 0, 0).
Proof. compute; reflexivity. Qed.
Example peven_test2 : test_ceval (update empty_state X 11) peven = Some (11, 0, 1).
Proof. compute; reflexivity. Qed.
Example peven_test3 : test_ceval (update empty_state X 12) peven = Some (12, 0, 0).
Proof. compute; reflexivity. Qed.
Example peven_test4 : test_ceval (update empty_state X 13) peven = Some (13, 0, 1).
Proof. compute; reflexivity. Qed.
Example peven_test5 : test_ceval (update empty_state X 14) peven = Some (14, 0, 0).
Proof. compute; reflexivity. Qed.

(* -----
  関係としての評価
-------- *)

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip :
      forall st,
      SKIP / st || st
  | E_Ass :
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
  where "c1 '/' st '||' st'" := (ceval c1 st st').

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
  ].

Example ceval_example1:
  (
    X ::= ANum 2;
    IFB
      BLe (AId X) (ANum 1)
    THEN
      Y ::= ANum 3
    ELSE
      Z ::= ANum 4
    FI
  ) / empty_state || (update (update empty_state X 2) Z 4).
Proof.
  apply E_Seq with (update empty_state X 2).
  Case "assignment command".
    apply E_Ass. reflexivity.
  Case "if command".
    apply E_IfFalse.
      reflexivity.
      apply E_Ass. reflexivity.
Qed.

(* 練習問題: ★★ (ceval_example2) *)
Example ceval_example2:
  (
    X ::= ANum 0;
    Y ::= ANum 1;
    Z ::= ANum 2
  ) / empty_state || (update (update (update empty_state X 0) Y 1) Z 2).
Proof with eauto using ceval.
  apply E_Seq with (st' := (update empty_state X 0))...
Qed.

(* -----
  関係による評価とステップ指数を利用した評価の等価性
-------- *)
Theorem ceval_step__ceval:
  forall c st st',
  (exists i, ceval_step st c i = Some st') ->
  c / st || st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].

  Case "i = 0 -- contradictory".
    intros c st st' H.
    inversion H.

  Case "i = S i'".
    intros c st st' H.
    com_cases (destruct c) SCase;
        simpl in H;
        inversion H;
        subst;
        clear H.

      SCase "SKIP".
        apply E_Skip.

      SCase "::=".
        apply E_Ass.
        reflexivity.

      SCase ";".
        remember (ceval_step st c1 i') as r1.
        destruct r1.
        
        SSCase "Evaluation of r1 terminates normally".
          apply E_Seq with s.
          apply IHi'. rewrite Heqr1. reflexivity.
          apply IHi'. simpl in H1. assumption.

        SSCase "Otherwise -- contradiction".
          inversion H1.

      SCase "IFB".
        remember (beval st b) as r.
        destruct r.

        SSCase "r = true".
          apply E_IfTrue.
          rewrite Heqr.
          reflexivity.
          apply IHi'.
          assumption.

        SSCase "r = false".
          apply E_IfFalse.
          rewrite Heqr.
          reflexivity.
          apply IHi'.
          assumption.

      SCase "WHILE".
        remember (beval st b) as r.
        destruct r.

        SSCase "r = true".
          remember (ceval_step st c i') as r1.
          destruct r1.

          SSSCase "r1 = Some s".
            apply E_WhileLoop with s.
            rewrite Heqr.
            reflexivity.
            apply IHi'.
            rewrite Heqr1.
            reflexivity.
            apply IHi'.
            simpl in H1.
            assumption.

          SSSCase "r1 = None".
            inversion H1.

        SSCase "r = false".
          inversion H1.
          apply E_WhileEnd.
          rewrite Heqr.
          subst.
          reflexivity.
Qed.

(* 練習問題: ★★★★ (ceval_step__ceval_inf) *)
(*

定理：あるiが存在してceval_step st c i = Some st'ならば、c / st || st'である。

証明：

iの帰納法による。

i = 0の場合：
  定理の仮定より、ceval_step st c 0 = Some st'である。
  しかし、ceval_stepの定義より、i = 0の場合はNoneになる。
  定理の仮定が成り立たないため、所望の結論は自明に満たされる。

i = i' + 1の場合：
  ceval_step st c (i' + 1) = Some st'を仮定して、c / st || st'を示す。
  また帰納法の仮定により、すべてのc、st、st'について「ceval_step st c i' = Some st'ならば、c / st || st'」が成り立つ。
  cのコンストラクタによって場合分けする。

  CSkipの場合：
    ceval_step st (CSkip) (i' + 1) = Some st'を仮定して、(CSkip) / st || st'を示す。
    ceval_stepの定義より、ceval_step st (CSkip) (i' + 1) = Some stである。
    仮定より、Some st = Some st'であり、st = st'である。
    したがって、(CSkip) / st || stを示せば良く、E_Skipより所望の結論が成り立つ。

  CAssの場合：
    ceval_step st (l ::= a1) (i' + 1) = Some st'を仮定して、l ::= a1 / st || st'を示す。
    ceval_stepの定義より、ceval_step st (l ::= a1) (i' + 1) (i' + 1) = Some (update st l (aeval st a1))である。
    仮定より、(update st l (aeval st a1)) = st'である。
    したがって、l ::= a1 / st || (update st l (aeval st a1))を示す。
    E_Assより、aeval st a1 = nとおくと、(l ::= a1) / st || (update st l n)であるため、所望の結論が成り立つ。

  CSeqの場合：
    ceval_step st (c1 ; c2) (i' + 1) = Some st''を仮定して、(c1 ; c2) / st || st''を示す。
    ceval_stepの定義より、ceval_step st c1 i'の結果によって場合分けする。

    Noneの場合：
      ceval_step st (c1 ; c2) (i' + 1) = Noneとなるが、これは仮定と矛盾するため、所望の結論は自明に満たされる。
    
    Some st'の場合：
      ceval_step st c1 i' = Some st'である。（1）
      ceval_step st (c1 ; c2) (i' + 1) = ceval_step st' c2 i' = Some st''である。
        特に、ceval_step st' c2 i' = Some st''である（2）
      1、2と帰納法の仮定より以下が成り立つ。
        c1 / st || st'
        c2 / st' || st''
      これらとE_Seqより(c1 ; c2) / st || st''が成り立つため、所望の結論が成り立つ。

  CIfの場合：
    ceval_step st (IFB b1 THEN c1 ELSE c2) (i' + 1) = Some st'を仮定して、(IFB b1 THEN c1 ELSE c2) / st || st'を示す。
    ceval_stepの定義より、beval st b1の真偽によって場合分けする。

    beval st b1 = trueの場合：
      ceval_step st (IFB b1 THEN c1 ELSE c2) (i' + 1) = ceval_step st c1 i' = Some st'である。
        特に、ceval_step st c1 i' = Some st'である
        帰納法の仮定により、c1 / st || st'である（1）
      beval st b1 = true、1、E_IfTrueより、(IFB b1 THEN c1 ELSE c2) / st || st'であるため、所望の結論が満たされる。

    beval st b1 = falseの場合：
      trueの場合と同様である。

  CWhileの場合：
    ceval_step st (WHILE b1 DO c1 END) (i' + 1) = Some st''を仮定して、(WHILE b1 DO c1 END) / st || st''を示す。
    ceval_stepの定義より、beval st b1の真偽によって場合分けする。

    beval st b1 = trueの場合：
      ceval_stepの定義より、ceval_step st c1 i'の結果によって場合分けする。

      Noneの場合：
        ceval_step st (WHILE b1 DO c1 END) (i' + 1) = Noneとなり、仮定が成り立たないため、所望の結論は自明に満たされる。
      
      Some st'の場合：
        ceval_step st c1 i' = Some st'である。
          帰納法の仮定より、c1 / st || st'である（1）
        ceval_step st (WHILE b1 DO c1 END) (i' + 1) = ceval_step st' (WHILE b1 DO c1 END) i' = Some st''である。
          特に、ceval_step st' (WHILE b1 DO c1 END) i' = Some st''である。
          帰納法の仮定より、(WHILE b1 DO c1 END) / st' || st''である（2）
        beval st b1 = true、1、2、E_WhileLoopより、(WHILE b1 DO c1 END) / st || st''であるため、所望の結論が成り立つ。

    beval st b1 = falseの場合：
      ceval_step st (WHILE b1 DO c1 END) (i' + 1) = Some st = Some st''である。
        特に、Some st = Some st''であり、st = st''である。
      したがって、(WHILE b1 DO c1 END) / st || stを示せば良い、
      これは、beval st b1 = falseとE_WhileEndによって示されるため、所望の結論が成り立つ。
*)

Theorem ceval_step_more: 
  forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
  induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
    Case "i1 = 0".
      inversion Hceval.
    Case "i1 = S i1'".
      destruct i2 as [|i2']. inversion Hle.
      assert (Hle': i1' <= i2') by lia.
      com_cases (destruct c) SCase.
      SCase "SKIP".
        simpl in Hceval. inversion Hceval.
        reflexivity.
      SCase "::=".
        simpl in Hceval. inversion Hceval.
        reflexivity.
      SCase ";".
        simpl in Hceval. simpl.
        remember (ceval_step st c1 i1') as st1'o.
        destruct st1'o.
        SSCase "st1'o = Some".
          symmetry in Heqst1'o.
          apply (IHi1' i2') in Heqst1'o; try assumption.
          rewrite Heqst1'o. simpl. simpl in Hceval.
          apply (IHi1' i2') in Hceval; try assumption.
        SSCase "st1'o = None".
          inversion Hceval.

      SCase "IFB".
        simpl in Hceval. simpl.
        remember (beval st b) as bval.
        destruct bval; apply (IHi1' i2') in Hceval; assumption.

      SCase "WHILE".
        simpl in Hceval. simpl.
        destruct (beval st b); try assumption.
        remember (ceval_step st c i1') as st1'o.
        destruct st1'o.
        SSCase "st1'o = Some".
          symmetry in Heqst1'o.
          apply (IHi1' i2') in Heqst1'o; try assumption.
          rewrite Heqst1'o. simpl. simpl in Hceval.
          apply (IHi1' i2') in Hceval; try assumption.
        SSCase "i1'o = None".
          simpl in Hceval. inversion Hceval.
Qed.

(* 練習問題: ★★★, recommended (ceval__ceval_step) *)
Theorem ceval__ceval_step:
  forall c st st',
  c / st || st' ->
  exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  ceval_cases (induction Hce) Case;
    try solve [
      subst;
      exists 1;
      simpl;
      reflexivity
    ].

  Case "E_Seq".
    inversion IHHce1 as [i1 IHHce1_inv].
    inversion IHHce2 as [i2 IHHce2_inv].
    exists (S (i1 + i2)).
    simpl.
    assert (i1i1i2: i1 <= i1 + i2) by lia.
    specialize (ceval_step_more _ _ _ _ _ i1i1i2 IHHce1_inv) as IHHce1_inv_i1i1i2.
    rewrite IHHce1_inv_i1i1i2.
    assert (i2i1i2: i2 <= i1 + i2) by lia.
    apply (ceval_step_more _ _ _ _ _ i2i1i2).
    assumption.

  Case "E_IfTrue".
    inversion IHHce as [i' IHHce_inv].
    exists (S i').
    simpl.
    rewrite H.
    assumption.

  Case "E_IfFalse".
    inversion IHHce as [i' IHHce_inv].
    exists (S i').
    simpl.
    rewrite H.
    assumption.

  Case "E_WhileEnd".
    exists 1.
    simpl.
    rewrite H.
    reflexivity.

  Case "E_WhileLoop".
    inversion IHHce1 as [i1 IHHce1_inv].
    inversion IHHce2 as [i2 IHHce2_inv].
    exists (S (i1 + i2)).
    simpl.
    rewrite H.
    assert (i1i1i2: i1 <= i1 + i2) by lia.
    specialize (ceval_step_more _ _ _ _ _ i1i1i2 IHHce1_inv) as IHHce1_inv_i1i1i2.
    rewrite IHHce1_inv_i1i1i2.
    assert (i2i1i2: i2 <= i1 + i2) by lia.
    apply (ceval_step_more _ _ _ _ _ i2i1i2).
    assumption.
Qed.

Theorem ceval_and_ceval_step_coincide:
  forall c st st',
  c / st || st'
  <-> ∃ i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split.
  apply ceval__ceval_step.
  apply ceval_step__ceval.
Qed.

(* -----
  実行の決定性
-------- *)
Theorem ceval_deterministic:
  forall c st st1 st2,
  c / st || st1 →
  c / st || st2 →
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  ceval_cases (induction E1) Case;
    intros st2 E2; inversion E2; subst.

  Case "E_Skip". reflexivity.

  Case "E_Ass". reflexivity.

  Case "E_Seq".
    assert (st' = st'0) as EQ1.
      SCase "Proof of assertion". apply IHE1_1; assumption.
    subst st'0.
    apply IHE1_2. assumption.

  Case "E_IfTrue".

    SCase "b1 evaluates to true".
      apply IHE1. assumption.

    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H5. inversion H5.

  Case "E_IfFalse".

    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H5. inversion H5.

    SCase "b1 evaluates to false".
      apply IHE1. assumption.

  Case "E_WhileEnd".

    SCase "b1 evaluates to true".
      reflexivity.

    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H2. inversion H2.

  Case "E_WhileLoop".

    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H4. inversion H4.

    SCase "b1 evaluates to false".
      assert (st' = st'0) as EQ1.
        SSCase "Proof of assertion". apply IHE1_1; assumption.
      subst st'0.
      apply IHE1_2. assumption.
Qed.

Theorem ceval_deterministic' :
  forall c st st1 st2,
  c / st || st1 →
  c / st || st2 →
  st1 = st2.
Proof.
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1].
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  lia. lia.
Qed.

(********************************
  プログラムの検証
*********************************)

(* -----
  基本的な例
-------- *)
Theorem plus2_spec :
  forall st n st',
  st X = n ->
  plus2 / st || st' →
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval.
  subst.
  apply update_eq.
Qed.

(* 練習問題: ★★★, recommended (XtimesYinZ_spec) *)
Theorem XtimesYinZ_spec :
  forall st x y st',
  st X = x ->
  st Y = y ->
  XtimesYinZ / st || st' ->
  st' Z = x * y.
Proof.
  intros st x y st' Hx Hy Heval.
  inversion Heval; subst.
  simpl.
  apply update_eq.
Qed.

(* 練習問題: ★★★, recommended (loop_never_stops) *)
Theorem loop_never_stops :
  forall st st',
  ~(loop / st || st').
Proof.
  intros st st' contra.
  unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef.
  induction contra;
    try solve [inversion Heqloopdef].

    inversion Heqloopdef; subst.
    inversion H.

    apply (IHcontra2 Heqloopdef).
Qed.

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP => true
  | _ ::= _ => true
  | c1 ; c2 => andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END => false
  end.

(* 練習問題: ★★, optional (no_whilesR) *)
Inductive no_whilesR: com -> Prop :=
  | NW_Skip :
      no_whilesR SKIP
  | NW_Ass : forall l a1,
      no_whilesR (l ::= a1)
  | NW_Seq : forall c1 c2,
      no_whilesR c1 ->
      no_whilesR c2 ->
      no_whilesR (c1 ; c2)
  | NW_If : forall b1 c1 c2,
      no_whilesR c1 ->
      no_whilesR c2 ->
      no_whilesR (IFB b1 THEN c1 ELSE c2 FI).

Theorem no_whiles_eqv :
  forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  intros.
  split.

  Case "->".
    intros.
    com_cases (induction c) SCase;
      try solve [
        auto using no_whilesR
      ].

    SCase ";".
      inversion H.
      apply Bool.andb_true_iff in H1.
      inversion H1.
      auto using no_whilesR.

    SCase "IFB".
      inversion H.
      apply Bool.andb_true_iff in H1.
      inversion H1.
      auto using no_whilesR.

    SCase "WHILE".
      inversion H.

  Case "<-".
    intros.
    com_cases (induction c) SCase;
      try solve [
        auto using no_whilesR
      ].

    SCase ";".
      simpl.
      apply Bool.andb_true_iff.
      split.
      inversion H; subst.
      auto.
      inversion H; subst.
      auto.

    SCase "IFB".
      simpl.
      apply Bool.andb_true_iff.
      split.
      inversion H; subst.
      auto.
      inversion H; subst.
      auto.

    SCase "WHILE".
      inversion H.
Qed.

(* 練習問題: ★★★★, optional (no_whiles_terminating) *)
Theorem no_whiles_terminating :
  forall c st,
  no_whilesR c ->
  (exists st', c / st || st').
Proof with eauto using ceval.
  intros.
  generalize dependent st.
  com_cases (induction c) Case; intros...
  Case ";".
    inversion H; subst.
    specialize (IHc1 H2 st) as Hc1_e.
    inversion Hc1_e as [st' Hc1].
    specialize (IHc2 H3 st') as Hc2_e.
    inversion Hc2_e as [st'' Hc2]...

  Case "IFB".
    inversion H; subst.
    specialize (IHc1 H2 st) as Hc1_e.
    inversion Hc1_e as [st_c1 Hc1].
    specialize (IHc2 H4 st) as Hc2_e.
    inversion Hc2_e as [st_c2 Hc2].
    specialize (Bool.bool_dec (beval st b) true) as Hbevalb.
    inversion Hbevalb...

    SCase "beval st b <> true".
      apply Bool.not_true_is_false in H0...

  Case "WHILE".
    inversion H.
Qed.

(* -----
  プログラム正当性 (Optional)
-------- *)
Print fact_body. Print fact_loop. Print fact_com.

Fixpoint real_fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

Definition fact_invariant (x : nat) (st : state) :=
  (st Y) * (real_fact (st Z)) = real_fact x.

Theorem fact_body_preserves_invariant:
  forall st st' x,
  fact_invariant x st ->
  st Z <> 0 ->
  fact_body / st || st' ->
  fact_invariant x st'.
Proof.
  unfold fact_invariant, fact_body.
  intros st st' x Hm HZnz He.
  inversion He; subst; clear He.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  unfold update. simpl.
  destruct (st Z) as [| z'].

    assert (ZZ: 0 = 0) by lia.
    apply HZnz in ZZ.
    inversion ZZ.

    rewrite <- Hm.
    replace (S z' - 1) with z' by lia.
    simpl.
    assert (H: real_fact z' + z' * real_fact z' = S z' * real_fact z') by lia.
    rewrite H.
    lia.
Qed.

Theorem fact_loop_preserves_invariant :
  forall st st' x,
  fact_invariant x st ->
  fact_loop / st || st' ->
  fact_invariant x st'.
Proof.
  intros st st' x H Hce.
  remember fact_loop as c.
  ceval_cases (induction Hce) Case;
              inversion Heqc; subst; clear Heqc.
  Case "E_WhileEnd".
    assumption.
  Case "E_WhileLoop".
    apply IHHce2.
      apply fact_body_preserves_invariant with st;
            try assumption.
      intros Contra. simpl in H0; subst.
      rewrite Contra in H0. inversion H0.
      reflexivity.
Qed.

Theorem guard_false_after_loop :
  forall b c st st',
  (WHILE b DO c END) / st || st' ->
  beval st' b = false.
Proof.
  intros b c st st' Hce.
  remember (WHILE b DO c END) as cloop.
  ceval_cases (induction Hce) Case;
     inversion Heqcloop; subst; clear Heqcloop.
  Case "E_WhileEnd".
    assumption.
  Case "E_WhileLoop".
    apply IHHce2. reflexivity.
Qed.

Theorem fact_com_correct :
  forall st st' x,
  st X = x ->
  fact_com / st || st' ->
  st' Y = real_fact x.
Proof.
  intros st st' x HX Hce.
  inversion Hce; subst; clear Hce.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  inversion H1; subst; clear H1.
  rename st' into st''. simpl in H5.
  remember (update (update st Z (st X)) Y 1) as st'.
  assert (fact_invariant (st X) st').
    subst. unfold fact_invariant, update. simpl. lia.
  assert (fact_invariant (st X) st'').
    apply fact_loop_preserves_invariant with st'; assumption.
  unfold fact_invariant in H0.
  apply guard_false_after_loop in H5. simpl in H5.
  destruct (st'' Z).
  Case "st'' Z = 0". simpl in H0. lia.
  Case "st'' Z > 0 (impossible)". inversion H5.
Qed.

(* 練習問題: ★★★★, optional (subtract_slowly_spec) *)
Definition ss_invariant (x : nat) (z : nat) (st : state) :=
  minus (st Z) (st X) = minus z x.

Theorem subtract_slowly_body_preserves_invariant :
  forall x z st st',
  ss_invariant x z st ->
  st X <> 0 ->
  subtract_slowly_body / st || st' ->
  ss_invariant x z st'.
Proof.
  intros x z st st' Hstinv Hxneq0 Hssbeval.
  unfold ss_invariant.
  inversion Hssbeval; subst.
  inversion H1; subst.
  inversion H4; subst.
  simpl in Hssbeval.
  simpl in H1.
  simpl in H4.
  simpl.
  rewrite update_eq.
  rewrite update_neq.
  rewrite update_eq.
  rewrite update_neq.
  assert (st Z - 1 - (st X - 1) = st Z - st X) by lia.
  rewrite H.
  apply Hstinv.
  auto.
  auto.
Qed.

Theorem subtract_slowly_preserves_invariant :
  forall x z st st',
  ss_invariant x z st ->
  subtract_slowly / st || st' ->
  ss_invariant x z st'
.
Proof.
  intros x z st st' Hstinv Hsseval.
  unfold ss_invariant.
  unfold ss_invariant in Hstinv.
  remember subtract_slowly as c.
  ceval_cases (induction Hsseval) Case;
    try solve [
      inversion Heqc
    ].

  Case "E_WhileEnd".
    assumption.

  Case "E_WhileLoop".
    inversion Heqc; subst.
    inversion H.
    apply Bool.eq_true_not_negb_iff in H1.
    apply Bool.not_true_is_false in H1.
    apply Nat.eqb_neq in H1.
    specialize (subtract_slowly_body_preserves_invariant _ _ _ st' Hstinv H1 Hsseval1) as Hssinvst'.
    apply IHHsseval2.
    auto.
    auto.
Qed.

Theorem subtract_slowly_correct :
  forall x z st st',
  st X = x ->
  st Z = z ->
  subtract_slowly / st || st' ->
  st' Z = minus z x.
Proof.
  intros x z st st' Hstx Hstz Hsseval.
  inversion Hsseval; subst.

  Case "E_WhileEnd".
    inversion H3.
    apply Bool.not_true_iff_false in H0.
    apply Bool.eq_true_negb_classical_iff in H0.
    apply Nat.eqb_eq in H0.
    rewrite H0.
    lia.

  Case "E_WhileLoop".
    rename st' into st''.
    rename st'0 into st'.

    assert (ss_invariant (st X) (st Z) st'').
    SCase "Proof of assertion".
      apply subtract_slowly_preserves_invariant with (st := st).
        unfold ss_invariant.
        reflexivity.

        assumption.
    
    unfold ss_invariant in H.

    specialize (guard_false_after_loop _ _ _ _ Hsseval) as Hguard.
    inversion Hguard as [H_x_eq_0]; subst.
    apply Bool.not_true_iff_false in H_x_eq_0.
    apply Bool.eq_true_negb_classical_iff in H_x_eq_0.
    apply Nat.eqb_eq in H_x_eq_0.

    rewrite H_x_eq_0 in H.
    rewrite Nat.sub_0_r in H.
    assumption.
Qed.

(********************************
  追加の練習問題
*********************************)
(* todo *)
