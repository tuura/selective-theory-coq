Require Import Hask.Control.Iso.
Require Import Hask.Prelude.
Require Import Reasoning.
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
Require Import Hask.Control.Selective.Rigid.Parametricity.
Require Import Hask.Control.Selective.Rigid.FunctorLaws.
Require Import Hask.Control.Selective.Rigid.ApplicativeLaws.

Set Universe Polymorphism.
Generalizable All Variables.

Section Select_SelectiveLaws_Proofs.

Import FunctorLaws.
Import ApplicativeLaws.
Import SelectiveParametricity.

Context (F : Type -> Type).
Context (FFunctor : Functor F).
Context (FFunctorLaws : FunctorLaws F).

(* -- P1id (Identity): select x (pure id) == either id id <$> x *)
Theorem Select_Selective_law1 `{Functor F} :
  forall (A B : Set) (x : Select F (A + B)) (y : A -> B),
    Select_select x (Pure y) = Select_map (either y id) x.
Proof.
  intros A B x y.
  rewrite Select_select_equation_1. now simpl.
Qed.

Theorem Select_Selective_law2_distr :
  forall (A B : Type)
    (x : A + B) (y : Select F (A -> B)) (z : Select F (A -> B)) ,
    pure x <*? (y *> z) = (pure x <*? y) *> (pure x <*? z).
Proof.
  intros A B x y z.
  `Begin
   (pure x <*? (y *> z)).
  ≡⟨ reflexivity ⟩
   (pure x <*? (liftA2 (const (@id (A -> B))) y z)).
  ≡⟨ reflexivity ⟩
   (pure x <*? (const (@id (A -> B)) <$> y <*> z)).
  ≡⟨ admit ⟩
   (pure x <*? (pure (const (@id (A -> B))) <*> y <*> z)).
  rewrite (@ap_fmap (Select F) Select_ApplicativeLaws).
  ≡⟨ admit ⟩
   (const (@id B) <$> (pure x <*? y) <*> (pure x <*? z)).
  ≡⟨ reflexivity ⟩
   (liftA2 (const (@id B)) (pure x <*? y) (pure x <*? z)).
  ≡⟨ reflexivity ⟩
   ((pure x <*? y) *> (pure x <*? z))
  `End.
Theorem select_selective_law3_assoc :
  forall (A B C : Set) `{FunctorLaws F}
  (x : Select F (B + C))
  (y : Select F (A + (B -> C)))
  (z : Select F (A -> B -> C)),
  x <*? (y <*? z) =
  ((fmap law3_f x) <*? (fmap law3_g y)) <*? (fmap law3_h z).
Proof.
Admitted.

End Select_SelectiveLaws_Proofs.
