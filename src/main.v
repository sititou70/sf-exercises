Require Import Unicode.Utf8.
Require Import _nat.

Notation "x + y" := (_plus x y) (at level 50, left associativity) : nat_scope.

Theorem plus_assoc :
  ∀ (n m p : _nat),
  n + (m + p) = n + m + p.
Proof.
  intros n m p.
  induction n.
  (* n = O *)
    reflexivity.
  (* n = S n' *)
    simpl.
    rewrite IHn.
    reflexivity.
Qed.
