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

Export FunctorLaws.

(* Check FunctorLaws. *)

Global Program Instance Select_FunctorLaws
       {F : Set -> Set} {HF : Functor F} {HFL : FunctorLaws F} : FunctorLaws (Select F).
(*   forall (x : Select F A), fmap id x = id x. *)
Obligation 1.
unfold id.
extensionality x.
generalize dependent x.
induction x; trivial.
rewrite Select_map_equation_2.
f_equal; repeat rewrite H_subst_id in *; rewrite fmap_id.
- unfold id. now rewrite IHx.
- now unfold id.
Qed.
(*   fmap f ∘ fmap g = fmap (f ∘ g). *)
Obligation 2.
extensionality x.
simpl.
revert B C f g.
induction x.
- trivial.
- intros b c f0 g.
  repeat rewrite Select_map_equation_2.
  f_equal.
  + rewrite <- fmap_comp. now rewrite IHx.
  + unfold "∘". now rewrite fmap_comp_x.
Qed.
(************************************************************)
