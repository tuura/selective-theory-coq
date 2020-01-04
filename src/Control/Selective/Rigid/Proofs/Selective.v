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
Require Import Hask.Control.Selective.Rigid.Proofs.Functor.
Require Import Hask.Control.Selective.Rigid.Proofs.Applicative.

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
  ≡⟨ now rewrite ap_fmap ⟩
   (pure x <*? (pure (const (@id (A -> B))) <*> y <*> z)).
  ≡⟨ reflexivity ⟩
   (pure x <*? ((Left <$> (pure (const (@id (A -> B))) <*> y)) <*? (rev_f_ap <$> z))).
  ≡⟨ now rewrite ap_fmap ⟩
   (pure x <*? (((Left <$> (const (@id (A -> B)) <$> y)) <*? (rev_f_ap <$> z)))).
  remember (const (@id (A -> B))) as g.
  ≡⟨ reflexivity ⟩
   (pure x <*? (((Left <$> (g <$> y)) <*? (rev_f_ap <$> z)))).
  ≡⟨ admit ⟩
   (pure x <*? (((mapLeft g <$> (Left <$> y)) <*? (rev_f_ap <$> z)))).
  ≡⟨ now setoid_rewrite free_theorem_2 ⟩
   (pure x <*? ((Left <$> y) <*? ((fun k => k ∘ g) <$> (rev_f_ap <$> z)))).
  ≡⟨ functor_laws ⟩
   (pure x <*? ((Left <$> y) <*? (((fun k => k ∘ g) ∘ rev_f_ap) <$> z))).
  ≡⟨ admit ⟩
   (pure x <*? ((Left <$> y) <*? (((fun k => k ∘ const id) ∘ (fun x k => k x)) <$> z))).
  clear Heqg g. set (g :=  ((fun k => k ∘ const id) ∘ (fun x k => k x))).
  ≡⟨ compute in g; now subst g ⟩
   (pure x <*? ((Left <$> y) <*? ((fun k => const k) <$> z))).
  ≡⟨ admit ⟩
   (pure x <*? ((Left <$> y) <*? ((fun k => const k) <$> z))).
  clear g. set (g := (fun k => const k)).
  ≡⟨ admit ⟩
   (pure x <*? (((Left <$> y) <*? ((fun k => k ∘ g) <$> (rev_f_ap <$> z))))).
  ≡⟨ admit ⟩
   (((pure (fmap (const (@id B)) x)) <*?
     ((fmap[→_] (const (@id B))) <$> y)) <*> (pure x <*? z)).
  ≡⟨ functor_laws ⟩
   ((((fmap (const (@id B))) <$> pure x) <*?
     ((fmap[→_] (const (@id B))) <$> y)) <*> (pure x <*? z)).
  ≡⟨ now rewrite <- free_theorem_1 ⟩
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
