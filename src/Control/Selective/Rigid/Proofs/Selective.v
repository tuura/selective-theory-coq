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
Require Import Hask.Control.Selective.Rigid.Proofs.Functor.
Require Import Hask.Control.Selective.Rigid.Proofs.Applicative.

Import FunctorLaws.
Import ApplicativeLaws.

Section WithF.
Context (F : Set -> Set).
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

Lemma Select_pure_right :
  forall (A B : Set) (x : B) (z : Select F A) (f : A -> (A -> B)),
  (* select (pure (Right x)) y = const x <$> y. *)
  select (pure (Right x)) (f <$> z) =
  const x <$> (f <$> z).
  (* select (pure (Right x)) (rev_f_ap <$> z). *)
Proof.
Admitted.

Theorem select_selective_law3_assoc :
  forall (A B C : Set)
  (x : Select F (B + C))
  (y : Select F (A + (B -> C)))
  (z : Select F (A -> B -> C)),
  x <*? (y <*? z) =
  ((fmap law3_f x) <*? (fmap law3_g y)) <*? (fmap law3_h z).
Proof.
Admitted.
End WithF.
