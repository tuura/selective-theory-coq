Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition undefined {a : Type} : a. Admitted.

Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

Definition flip `(f : a -> b -> c) : b -> a -> c := fun y x => f x y.

Definition const {A B : Type} (x : B) : A -> B := fun _ => x.

Definition apply `(f : a -> b) (x : a) : b := f x.

Definition uncurry `(f : a -> b -> c) : (a * b -> c) :=
  fun z => f (fst z) (snd z).

Notation "f .: g" := (fun x y => f (g x y)) (at level 100).

(*
Lemma sym_neg : forall a (R : rel a), symmetric R -> symmetric (negb .: R).
Proof.
  move=> a R H x y.
  by rewrite H.
Qed.
*)
