Require Import Hask.Prelude.
Require Import Omega.

Ltac inv H  := inversion H; subst; simpl; clear H.
Ltac contra := intros top; contradiction top; clear top.
Ltac invert := intros top; inversion top; clear top.

Tactic Notation "invert" "as" simple_intropattern(pat) :=
  intros top; inversion top as pat; clear top.

Lemma ltn_leq_trans : forall n m p : nat, m < n -> n <= p -> m < p.
Proof. intros. omega. Qed.

Definition comp {a b c} (f : b -> c) (g : a -> b) (x : a) : c := f (g x).
Arguments comp {a b c} f g x /.

Infix "\o" := comp (at level 50).

Theorem comp_id_left : forall {A B : Set} (f : A -> B), id \o f = f.
Proof. reflexivity. Qed.

Hint Resolve comp_id_left.

Theorem comp_id_right : forall {A B : Set} (f : A -> B), f \o id = f.
Proof. reflexivity. Qed.

Hint Resolve comp_id_right.

Theorem comp_assoc : forall {A B C D : Set} (f : C -> D) (g : B -> C) (h : A -> B),
  f \o (g \o h) = (f \o g) \o h.
Proof. reflexivity. Qed.

Hint Resolve comp_assoc.

Theorem uncompose : forall {A B C : Set} (f : B -> C) (g : A -> B) (x : A) (y : C),
  (f \o g) x = f (g x).
Proof. reflexivity. Qed.

Ltac uncompose k :=
  rewrite <- (uncompose k);
  repeat (rewrite <- comp_assoc).
