Require Import Unicode.Utf8.
Require Import commons.

(********************************
  列挙型
*********************************)

(* -----
  曜日の表し方
-------- *)
Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Eval simpl in (next_weekday friday).
Eval simpl in (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof.
  simpl.
  reflexivity.
Qed.

(* -----
  ブール型
-------- *)
Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true ) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true ) = true.
Proof. simpl. reflexivity. Qed.

(* 練習問題: ★ (nandb) *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  negb (andb b1 b2).
Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(* 練習問題: ★ (andb3) *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  andb (andb b1 b2) b3.
Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(* -----
  関数の型
-------- *)
Check (negb true).
Check negb.

(* -----
  数値
-------- *)
Module Playground1.
  Inductive nat : Type :=
    | O : nat
    | S : nat → nat.

  Definition pred (n : nat) : nat :=
    match n with
      | O => O
      | S n' => n'
    end.
End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check (S (S (S (S O)))).
Eval simpl in (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : bool :=
  negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. simpl. reflexivity. Qed.

Module Playground2.
  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
      | O => m
      | S n' => S (plus n' m)
    end.
  Eval simpl in (plus (S (S (S O))) (S (S O))).

  Fixpoint mult (n m : nat) : nat :=
    match n with
      | O => O
      | S n' => plus m (mult n' m)
    end.
  Example test_mult1: (mult 3 3) = 9.
  Proof. simpl. reflexivity. Qed.

  Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | O , _ => O
    | S _ , O => n
    | S n', S m' => minus n' m'
    end.
End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

(* 演習問題: ★ (factorial) *)
Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.
Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.
Check ((0 + 1) + 1).

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

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.
Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* 練習問題: ★★ (blt_nat) *)
Definition blt_nat (n m : nat) : bool :=
  if beq_nat n m then false else ble_nat n m.
Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

(********************************
  簡約を用いた証明
*********************************)
Theorem plus_O_n : ∀ n : nat, 0 + n = n.
Proof.
  simpl. reflexivity. Qed.

Theorem plus_O_n' : ∀ n : nat, 0 + n = n.
Proof.
  reflexivity. Qed.

(* 練習問題: ★, optional (simpl_plus) *)
Eval simpl in (∀ n : nat, n + 0 = n).
Eval simpl in (∀ n : nat, 0 + n = n).
(*
前者は「∀ n : nat, n + 0 = n : Prop」で、命題がそのまま型になっているsimplは特に作用していない。
後者は「∀ n : nat, n = n : Prop」で、simplによって命題が簡約されている。これはplusの定義からすぐにわかるからである。
*)

(********************************
  introsタクティック
*********************************)
Theorem plus_O_n'' : ∀ n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_1_l : ∀ n : nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : ∀ n : nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

(********************************
  書き換え（Rewriting）による証明
*********************************)
Theorem plus_id_example :
  ∀ n m:nat,
  n = m →
  n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

(* 練習問題: ★ (plus_id_exercise) *)
Theorem plus_id_exercise :
  ∀ n m o : nat,
  n = m →
  m = o →
  n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
Qed.

Theorem mult_0_plus :
  ∀ n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.

(* 練習問題: ★★, recommended (mult_1_plus) *)
Theorem mult_1_plus :
  ∀ n m : nat,
  (1 + n) * m = m + (n * m).
Proof.
  intros n m.
  reflexivity.
Qed.
(* see: http://io.kuis.kyoto-u.ac.jp/~igarashi/class/cal12w/slides3.pdf *)

(********************************
  Case分析
*********************************)
Theorem plus_1_neq_0_firsttry :
  ∀ n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. simpl. Admitted.

Theorem plus_1_neq_0 :
  ∀ n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n'].
  reflexivity.
  reflexivity.
Qed.

Theorem negb_involutive :
  ∀ b : bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

(* 練習問題: ★ (zero_nbeq_plus_1) *)
Theorem zero_nbeq_plus_1 :
  ∀ n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  destruct n as [| n'].
  reflexivity.
  reflexivity.
Qed.

(********************************
  Caseへのネーミング
*********************************)
Theorem andb_true_elim1 :
  ∀ b c : bool,
  andb b c = true →
  b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity.
Qed.

(* 練習問題: ★★ (andb_true_elim2) *)
Theorem andb_true_elim2 :
  ∀ b c : bool,
  andb b c = true →
  c = true.
Proof.
  intros b c H.
  destruct c.
  Case "c = true".
    reflexivity.
  Case "c = false".
    rewrite <- H.
    destruct b.
    SCase "b = true".
      reflexivity.
    SCase "b = false".
      reflexivity.
Qed.

(********************************
  帰納法
*********************************)
Theorem plus_0_r_firsttry :
  ∀ n : nat,
  n + 0 = n.
Proof.
  intros n.
  simpl. Admitted.

Theorem plus_0_r_secondtry :
  ∀ n : nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. Admitted.

Theorem plus_0_r :
  ∀ n : nat,
  n + 0 = n.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem minus_diag :
  ∀ n,
  minus n n = 0.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    simpl.
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

(* 練習問題: ★★, recommended (basic_induction) *)
Theorem mult_0_r :
  ∀ n : nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_n_Sm :
  ∀ n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_comm :
  ∀ n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n'].
  Case "n = 0".
    rewrite -> plus_O_n.
    rewrite -> plus_0_r.
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(* 練習問題: ★★ (double_plus) *)
Lemma double_plus :
  ∀ n,
  double n = n + n .
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

(* 練習問題: ★ (destruct_induction) *)
(*
inductionは帰納法を実行する。帰納法の仮定をコンテキストに導入する。
destructは帰納法を実行せず、値の形によって場合分けしているだけである。
*)

(********************************
  形式的証明と非形式的証明
*********************************)
Theorem plus_assoc' : ∀ n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_assoc : ∀ n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.
Qed.

(* 練習問題: ★★ (plus_comm_informal) *)
(*
定理：任意のn, mについて、以下が成り立つ。
  n + m = m + n
証明：
  nについて帰納法を適用する。
  n = 0の場合：
    0 + m = m + 0となり、これは加法の定義から直接導くことができる。
  n = S n'の場合：
    S n' + m = m + S n'となる。
    Sの定義より
    S (n' + m) = m + S n'
    帰納法の仮定より
    S (m + n') = m + S n'
    plus_n_Smより
    m + S n' = m + S n'
  したがって所望の結論が得られた。
*)

(* 練習問題: ★★, optional (beq_nat_refl_informal) *)
(*
定理：任意のnについて、以下が成り立つ
  true=beq_nat n n（nはnと等しいという命題がtrueとなる）
証明：
  nについて帰納法を適用する。
  n = 0の場合：
    beq_natの定義より自明である。
  n = S n'の場合：
    beq_nat (S n') (S n')
    beq_natの定義より
    beq_nat n' n'
    帰納法の仮定よりこれはtrueである。
  したがって所望の結論が得られた。
*)

(* 練習問題: ★, optional (beq_nat_refl) *)
Theorem beq_nat_refl :
  ∀ n : nat,
  true = beq_nat n n.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

(********************************
  証明の中で行う証明
*********************************)
Theorem mult_0_plus' :
  ∀ n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
  Case "Proof of assertion".
    reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange_firsttry :
  ∀ n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite -> plus_comm.
  Admitted.

Theorem plus_rearrange :
  ∀ n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  Case "Proof of assertion".
    rewrite -> plus_comm.
    reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

(* 練習問題: ★★★★ (mult_comm) *)
Theorem plus_swap :
  ∀ n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  assert (H2: n + m = m + n).
  Case "Proof of assertion".
    rewrite -> plus_comm.
    reflexivity.
  rewrite -> H2.
  rewrite -> plus_assoc.
  reflexivity.
Qed.

Theorem mult_comm :
  ∀ m n : nat,
  m * n = n * m.
Proof.
  intros n m.
  induction n as [| n'].
  Case "n = 0".
    simpl.
    rewrite mult_0_r.
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
      assert (H: ∀ x y : nat, x + x * y = x * S y).
      SCase "Proof of assertion".
        intros.
        induction x as [| x'].
        SSCase "x = 0".
          reflexivity.
        SSCase "x = S x'".
          simpl.
          rewrite -> plus_swap.
          rewrite -> IHx'.
          reflexivity.
  rewrite -> H.
  reflexivity.  
Qed.

(* 練習問題: ★★, optional (evenb_n__oddb_Sn) *)
Theorem evenb_n__oddb_Sn :
  ∀ n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    assert (H: ∀ x : nat, evenb (S (S x)) = evenb x).
    SCase "Proof of assertion".
      induction x as [| x'].
      SSCase "x = 0".
        reflexivity.
      SSCase "x = S x'".
        reflexivity.
    rewrite -> H.
    rewrite -> IHn'.
    rewrite -> negb_involutive.
    reflexivity.
Qed.

(********************************
  さらなる練習問題
*********************************)

(* TODO *)
