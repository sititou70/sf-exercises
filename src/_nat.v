Require Import Unicode.Utf8.

Inductive _nat : Type :=
  | O : _nat
  | S : _nat → _nat.

Fixpoint _plus (n : _nat) (m : _nat) : _nat :=
  match n with
  | O => m
  | S n' => S (_plus n' m)
  end.
