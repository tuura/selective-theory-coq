Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Coq.Program.Basics.

Definition undefined {a : Type} : a. Admitted.

Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

Definition flip `(f : a -> b -> c) : b -> a -> c := fun y x => f x y.

Definition const {A B : Type} (x : B) : A -> B := fun _ => x.

Definition uncurry `(f : a -> b -> c) : (a * b -> c) :=
  fun z => f (fst z) (snd z).

Notation "f .: g" := (fun x y => f (g x y)) (at level 100).

(* Function application *)
Definition f_ap {A B : Type}
  (f : A -> B) (x : A) := f x.

(* Reverse function application *)
Definition rev_f_ap {A B : Set}
  (x : A) (f : A -> B) := f x.
