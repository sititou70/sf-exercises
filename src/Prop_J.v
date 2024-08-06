Require Import Unicode.Utf8.
Require Import commons.

(********************************
  命題によるプログラミング
*********************************)
Check (2 + 2 = 4).

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.
Check (ble_nat 3 2 = false).

Check (2 + 2 = 5).

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity. Qed.

Definition strange_prop1 : Prop :=
  (2 + 2 = 5) → (99 + 26 = 42).

Definition strange_prop2 :=
  ∀ n, (ble_nat n 17 = true) → (ble_nat n 99 = true).

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.
Definition even (n : nat) : Prop :=
  evenb n = true.
Check even.
Check (even 4).
Check (even 3).

Definition even_n__even_SSn (n : nat) : Prop :=
  (even n) → (even (S (S n))).

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

Definition teen : nat → Prop := between 13 19.

Definition true_for_zero (P : nat → Prop) : Prop :=
  P 0.

Definition true_for_n__true_for_Sn (P : nat → Prop) (n : nat) : Prop :=
  P n → P (S n).

Definition preserved_by_S (P : nat → Prop) : Prop :=
  ∀ n', P n' → P (S n').

Definition true_for_all_numbers (P : nat → Prop) : Prop :=
  ∀ n, P n.

Definition our_nat_induction (P : nat → Prop) : Prop :=
  (true_for_zero P) →
  (preserved_by_S P) →
  (true_for_all_numbers P).

(********************************
  根拠
*********************************)

(* -----
  帰納的に定義された命題
-------- *)
Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Inductive good_day : day → Prop :=
  | gd_sat : good_day saturday
  | gd_sun : good_day sunday.

Theorem gds : good_day sunday.
Proof. apply gd_sun. Qed.

Inductive day_before : day → day → Prop :=
  | db_tue : day_before tuesday monday
  | db_wed : day_before wednesday tuesday
  | db_thu : day_before thursday wednesday
  | db_fri : day_before friday thursday
  | db_sat : day_before saturday friday
  | db_sun : day_before sunday saturday
  | db_mon : day_before monday sunday.

Inductive fine_day_for_singing : day → Prop :=
  | fdfs_any : ∀ d : day, fine_day_for_singing d.

Theorem fdfs_wed : fine_day_for_singing wednesday.
Proof. apply fdfs_any. Qed.

(* -----
  証明オブジェクト
-------- *)
Definition fdfs_wed' : fine_day_for_singing wednesday :=
  fdfs_any wednesday.
Check fdfs_wed.
Check fdfs_wed'.

Inductive ok_day : day → Prop :=
  | okd_gd : ∀ d,
      good_day d →
      ok_day d
  | okd_before : ∀ d1 d2,
      ok_day d2 →
      day_before d2 d1 →
      ok_day d1.

Definition okdw : ok_day wednesday :=
  okd_before wednesday thursday
    (okd_before thursday friday
       (okd_before friday saturday
         (okd_gd saturday gd_sat)
         db_sat)
       db_fri)
    db_thu.

Theorem okdw' : ok_day wednesday.
Proof.
  apply okd_before with (d2 := thursday).
    apply okd_before with (d2 := friday).
      apply okd_before with (d2 := saturday).
          apply okd_gd. apply gd_sat.
          apply db_sat.
      apply db_fri.
  apply db_thu. Qed.

Print okdw'.

(* -----
  含意
-------- *)
Definition okd_before2 :=
  ∀ d1 d2 d3,
  ok_day d3 →
  day_before d2 d1 →
  day_before d3 d2 →
  ok_day d1.

(* 練習問題: ★, optional (okd_before2_valid) *)
Theorem okd_before2_valid : okd_before2.
Proof.
  unfold okd_before2.
  intros.
  apply okd_before with (d2 := d2).
  apply okd_before with (d2 := d3).
  apply H.
  apply H1.
  apply H0.
Qed.

Print okd_before2_valid.

(* -----
  帰納的に定義された型に対する帰納法の原理
-------- *)
Check nat_ind.

Theorem mult_0_r' :
  ∀ n : nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  Case "O". reflexivity.
  Case "S". simpl. intros n IHn. rewrite -> IHn.
    reflexivity. Qed.

(* 練習問題: ★★ (plus_one_r') *)
Theorem plus_one_r' :
  ∀ n : nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  Case "O".
    reflexivity.
  Case "S".
    simpl.
    intros.
    rewrite -> H.
    reflexivity.
Qed.

Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.
Check yesno_ind.

(* 練習問題: ★ (rgb) *)
Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.
Check rgb_ind.

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat → natlist → natlist.
Check natlist_ind.

(* 練習問題: ★ (natlist1) *)
Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 → nat → natlist1.
Check natlist1_ind.

(* 練習問題: ★ (ExSet) *)
Inductive ExSet : Type :=
  | con1 : bool -> ExSet
  | con2 : nat -> ExSet -> ExSet
.
Check ExSet_ind.

(* 練習問題: ★ (tree) *)
Inductive tree (X : Type) : Type :=
  | leaf : X → tree X
  | node : tree X → tree X → tree X.
Check tree_ind.

(* 練習問題: ★ (mytype) *)
Inductive mytype (X : Type) : Type :=
  | constr1 : X -> mytype X
  | constr2 : nat -> mytype X
  | constr3 : mytype X -> nat -> mytype X.
Check mytype_ind.

(* 練習問題: ★, optional (foo) *)
Inductive foo (X Y : Type) : Type :=
  | bar : X -> foo X Y
  | baz : Y -> foo X Y
  | quux : (nat -> foo X Y) -> foo X Y.
Check foo_ind.

(* 練習問題: ★, optional (foo') *)
Inductive foo' (X : Type) : Type :=
  | C1 : list X → foo' X → foo' X
  | C2 : foo' X.
Check foo'_ind.

(* -----
  帰納法の仮定
-------- *)
Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

Definition P_m0r' : nat→Prop :=
  fun n => n * 0 = 0.

Theorem mult_0_r'' : ∀ n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  Case "n = O". reflexivity.
  Case "n = S n'".
    unfold P_m0r. simpl. intros n' IHn'.
    apply IHn'. Qed.

(* -----
  偶数について再び
-------- *)
Inductive ev : nat → Prop :=
  | ev_0 : ev O
  | ev_SS : ∀ n : nat, ev n → ev (S (S n)).

(* 練習問題: ★, optional (four_ev) *)
Theorem four_ev' :
  ev 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.
Definition four_ev : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

(* 練習問題: ★★ (ev_plus4) *)
Definition ev_plus4 : ∀ n, ev n → ev (4 + n) :=
  fun (n : nat) (evn : ev n) =>
    ev_SS (2 + n) (ev_SS n evn).
Theorem ev_plus4' :
  ∀ n,
  ev n → ev (4 + n).
Proof.
  intros.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.
Print ev_plus4'.

(* 練習問題: ★★ (double_even) *)
Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
Theorem double_even : ∀ n,
  ev (double n).
Proof.
  intros.
  induction n as [| n'].
  Case "n = 0".
    simpl.
    apply ev_0.
  Case "n = S n'".
    simpl.
    apply ev_SS.
    apply IHn'.
Qed.

(* 練習問題: ★★★★, optional (double_even_pfobj) *)
Theorem double_even_for_print : ∀ n,
  ev (double n).
Proof.
  intros.
  induction n as [| n'].

    simpl.
    apply ev_0.

    simpl.
    apply ev_SS.
    apply IHn'.
Qed.
Print double_even_for_print.
Check nat_ind.
Definition double_even_obj : ∀ n : nat, ev (double n) :=
  fun n : nat =>
    nat_ind
      (fun n : nat => ev (double n))
      ev_0
      (fun (n' : nat) (IHn' : ev (double n')) =>
        ev_SS (double n') IHn'
      )
    n.

(* -----
  根拠に対する帰納法の推論
-------- *)

Theorem ev_minus2:
  ∀ n,
  ev n →
  ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  Case "E = ev_0".
    simpl.
    apply ev_0.
  Case "E = ev_SS n' E'".
    simpl.
    apply E'.
Qed.

(* 練習問題: ★ (ev_minus2_n) *)
Theorem ev_minus2_n:
  ∀ n,
  ev n →
  ev (pred (pred n)).
Proof.
  intros n E.
  destruct n as [| n'].
  Case "n = 0".
    simpl.
    apply ev_0.
  Case "n = S n'".
    simpl.
    (*
      ここでev (S n')からev (Nat.pred n')を示さないといけないが、
      それがまさにev_minus2であり、うまくいかない
    *)
    Admitted.

Theorem ev_even :
  ∀ n,
  ev n →
  even n.
Proof.
  intros n E.
  induction E as [| n' E'].
  Case "E = ev_0".
    unfold even.
    reflexivity.
  Case "E = ev_SS n' E'".
    unfold even.
    apply IHE'.
Qed.

(* 練習問題: ★ (ev_even_n) *)
Theorem ev_even_n :
  ∀ n,
  ev n →
  even n.
Proof.
  intros n E.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    (*
      ここでeven (S n')を示さないといけない。使える仮定は2つあるがどちらもうまく行かない
      仮定「ev (S n')」は、命題を言い換えているだけで使えない。
      仮定「ev n' → even n'」はn - 1の場合についてのものだが、そもそもnが偶数であるから前提が矛盾していて使えない。
    *)
    Admitted.

(* 練習問題: ★ (l_fails) *)
Theorem l :
  ∀ n,
  ev n.
Proof.
  intros n.
  induction n.
    Case "O".
      simpl.
      apply ev_0.
    Case "S".
      (*
        示したい結論「ev (S n)」が仮定「ev n」に矛盾しているから。
      *)
      Admitted.

(* 練習問題: ★★ (ev_sum) *)
Theorem ev_sum :
  ∀ n m,
  ev n →
  ev m →
  ev (n + m).
Proof.
  intros.
  induction H as [| n' H'].
  Case "H = ev_0".
    apply H0.
  Case "H = ev_SS n' H'".
    simpl.
    apply ev_SS.
    apply IHH'.
Qed.

Theorem SSev_ev_firsttry :
  ∀ n,
  ev (S (S n)) →
  ev n.
Proof.
  intros n E.
  destruct E as [| n' E'].
  Admitted.

Theorem SSev_even :
  ∀ n,
  ev (S (S n)) →
  ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  apply E'.
Qed.

(* 練習問題: ★ (inversion_practice) *)
Theorem SSSSev_even :
  ∀ n,
  ev (S (S (S (S n)))) →
  ev n.
Proof.
  intros.
  inversion H as [| n' H'].
  inversion H' as [| n'' H''].
  apply H''.
Qed.
Theorem even5_nonsense :
  ev 5 → 2 + 2 = 9.
Proof.
  intros.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

Theorem ev_minus2':
  ∀ n,
  ev n →
  ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  Case "E = ev_0".
    simpl.
    apply ev_0.
  Case "E = ev_SS n' E'".
    simpl.
    apply E'.
Qed.

(* 練習問題: ★★★ (ev_ev_even) *)
Theorem ev_ev_even :
  ∀ n m,
  ev (n + m) →
  ev n →
  ev m.
Proof.
  intros n m Hnm Hn.
  induction Hn as [| n' Hn'].
  Case "Hn = ev_0".
    apply Hnm.
  Case "Hn = ev_SS n' Hn'".
    apply IHHn'.
    inversion Hnm as [| n'' Hnm'].
    apply Hnm'.
Qed.

(* 練習問題: ★★★, optional (ev_plus_plus) *)
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
Theorem ev_plus_plus :
  ∀ n m p,
  ev (n + m) →
  ev (n + p) →
  ev (m + p).
Proof.
  intros n m p Hnm Hnp.
  apply ev_ev_even with (n := n + n).
  Case "ev (n + n + (m + p))".
    assert (H: n + n + (m + p) = n + m + (n + p)).
      rewrite <- PeanoNat.Nat.add_assoc.
      assert (Hswap: n + (m + p) = m + (n + p)).
        apply PeanoNat.Nat.add_shuffle3.
      rewrite -> Hswap.
      apply PeanoNat.Nat.add_assoc.
    rewrite H.
    apply ev_sum.
      apply Hnm.
      apply Hnp.
  Case "ev (n + n)".
    rewrite <- double_plus.
    apply double_even.
Qed.

(* -----
  なぜ命題を帰納的に定義するのか?
-------- *)

Inductive MyProp : nat → Prop :=
  | MyProp1 : MyProp 4
  | MyProp2 : ∀ n : nat, MyProp n → MyProp (4 + n)
  | MyProp3 : ∀ n : nat, MyProp (2 + n) → MyProp n.

Theorem MyProp_ten : MyProp 10.
Proof.
  apply MyProp3. simpl.
  assert (12 = 4 + 8) as H12.
    Case "Proof of assertion". reflexivity.
  rewrite -> H12.
  apply MyProp2.
  assert (8 = 4 + 4) as H8.
    Case "Proof of assertion". reflexivity.
  rewrite -> H8.
  apply MyProp2.
  apply MyProp1.
Qed.

(* 練習問題: ★★ (MyProp) *)
Theorem MyProp_0 : MyProp 0.
Proof.
  apply MyProp3.
  apply MyProp3.
  apply MyProp1.
Qed.
Theorem MyProp_plustwo :
  ∀ n : nat,
  MyProp n →
  MyProp (S (S n)).
Proof.
  intros.
  induction H as [| mp2n mp2H | mp3n mp3H].
  Case "H = MyProp1".
    apply MyProp2.
    apply MyProp3.
    apply MyProp1.
  Case "H = MyProp2 mp2n mp2H".
    apply MyProp2.
    apply IHmp2H.
  Case "H = MyProp3 mpp3n mp3H".
    apply MyProp3.
    apply IHmp3H.
Qed.

Theorem MyProp_ev :
  ∀ n : nat,
  ev n →
  MyProp n.
Proof.
  intros n E.
  induction E as [| n' E'].
  Case "E = ev_0".
    apply MyProp_0.
  Case "E = ev_SS n' E'".
    apply MyProp_plustwo. apply IHE'.
Qed.

(* 練習問題: ★★★ (ev_MyProp) *)
Theorem ev_MyProp :
  ∀ n : nat,
  MyProp n →
  ev n.
Proof.
  intros.
  induction H as [| mp2n mp2H | mp3n mp3H].
  Case "H = MyProp1".
    apply ev_SS.
    apply ev_SS.
    apply ev_0.
  Case "H = MyProp2 mp2n mp2H".
    apply ev_SS.
    apply ev_SS.
    apply IHmp2H.
  Case "H = MyProp3 mpp3n mp3H".
    inversion IHmp3H.
    apply H0.
Qed.

(* 練習問題: ★★★, optional (ev_MyProp_informal) *)
(*
定理：すべての自然数nに対して、MyProp nならばev n。

証明：

MyProp nの各コンストラクタについて、帰納法を適用する。

MyProp1の場合：
  n = 4であり、ev 4を示せば良い。
  そのためには、ev_SSより、ev 2を示せば良い。さらにev_SSよりev 0を示せば良い。
  ここで、ev_0よりev 0を示せるため、所望の結論が満たされる。
MyProp2の場合：
  n = 4 + n'であり、帰納法の仮定はev n'である。ここでev (4 + n')を示せば良い。
  そのためには、ev_SSよりev (2 + n')を示せば良い。さらにev_SSよりev n'を示せば良い。
  これは帰納法の仮定であるため所望の結論が満たされる。
MyProp3の場合：
  n = n'であり、帰納法の仮定はev (2 + n')である。ここでev n'を示せば良い。
  帰納法の仮定について、その導出に使われた各コンストラクタについて場合分けを行うと、
    ev_oの場合：
      0 = 2 + n'となり矛盾する。したがって、所望の結論は自明に満たされる。
    ev_SSの場合：
      2 + n' = S (S n')であり、ev n'であるため、所望の結論は満たされる。
*)
