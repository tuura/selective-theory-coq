Require Import FunctionalExtensionality.

Definition undefined {a : Set} : a. Admitted.

Definition id {A : Set} : A -> A := fun x => x.

Definition comp {A B C : Set} (f : B -> C) (g : A -> B) (x : A) : C := f (g x).
Arguments comp {_ _ _} f g x /.

Infix "∘" := comp (at level 50).

Lemma comp_assoc : forall {A B C D : Set} (f : C -> D) (g : B -> C) (h : A -> B),
      f ∘ (g ∘ h) = (f ∘ g) ∘ h.
Proof. reflexivity. Qed.

Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

Definition flip {A B C : Set} (f : A -> B -> C) : B -> A -> C := fun y x => f x y.

Definition const {A B : Set} (x : B) : A -> B := fun _ => x.

Definition uncurry {A B C : Set} (f : A -> B -> C) : (A * B -> C) :=
  fun z => f (fst z) (snd z).

(* Notation "f .: g" := (fun x y => f (g x y)) (at level 100). *)

(* Function application *)
Definition f_ap {A B : Set}
  (f : A -> B) (x : A) := f x.

(* Reverse function application *)
Definition rev_f_ap {A B : Set}
  (x : A) (f : A -> B) := f x.

Lemma flip_id_rev_f_ap : forall (A : Set), flip (@id (A -> A)) = (@rev_f_ap A A).
Proof. intros A. now extensionality a. Qed.

Lemma id_expand : forall (A : Set), flip rev_f_ap (@id A) = id.
Proof. intros A. now extensionality a. Qed.

(** Tactic helpers *)

Require Import FunctionalExtensionality.

Ltac extensionalize :=
  intuition;
  unfold comp, id; simpl;
  let A := fresh "A" in
  try extensionality A;
  let B := fresh "B" in
  try extensionality B;
  let C := fresh "C" in
  try extensionality C;
  try destruct A;
  try destruct B;
  try destruct C;
  simpl in *;
  repeat (match goal with
          | [ H : False    |- _ ] => contradiction H
          | [ H : unit     |- _ ] => destruct H
          | [ H : bool     |- _ ] => destruct H
          | [ H : sum _ _  |- _ ] => destruct H
          | [ H : prod _ _ |- _ ] => destruct H
          end);
  auto.
