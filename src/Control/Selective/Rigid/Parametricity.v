Require Import Hask.Prelude.
Require Import Data.Functor.
Require Import Data.Either.
Require Import Control.Applicative.
Require Import Control.Selective.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Equations.Equations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Hask.Control.Selective.Rigid.

Section WithF.
  Context {F : Set -> Set}.
  Context {HF : Functor F}.

Theorem free_theorem_1_MkSelect :
  forall (A B C : Set) (f : B -> C)
         (x : Select F (A + B)%type)
         (y : F (A -> B)),
    f <$> (MkSelect x y) =
    MkSelect (fmap[Either A] f <$> x)
             (fmap[Env A] f <$> y).
Proof.
  intros. simpl fmap. reflexivity.
Qed.

Axiom free_theorem_2_MkSelect :
  forall (A B C : Set) (f : A -> C) (x : Select F (A + B)) (y : F (C -> B)),
    MkSelect (mapLeft f <$> x) y = MkSelect x (fmap (fun g : C -> B => g ∘ f) y).

Axiom free_theorem_3_MkSelect :
  forall (A B C : Set) (f : C -> A -> B)
                   (x : Select F (A + B))
                   (y : F C),
    MkSelect x (f <$> y) = MkSelect (mapLeft (flip f) <$> x) (rev_f_ap <$> y).
End WithF.
