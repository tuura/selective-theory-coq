Require Import Coq.Program.Basics.
Require Import Hask.Prelude.
Require Import Data.Either.
Require Import Data.Monoid.
Require Import Data.Functor.
Require Import Control.Applicative.
Require Import Control.Selective.
(* Require Import Data.Over. *)
Require Import Coq.Strings.String.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Classes.Morphisms_Prop.
Require Import FunctionalExtensionality.

Generalizable All Variables.
(* Functors preserve extensional equality for the applied function.
   This is needed to perform setoid rewriting within the function
   passed to a functor. *)
Add Parametric Morphism {A B} `{Functor F} : (@fmap F _ A B)
  with signature (pointwise_relation _ eq ==> eq ==> eq)
    as mul_isomorphism.
Proof.
  intros.
  f_equal.
  extensionality e.
  apply H0.
Qed.


Inductive FreeA (f : Type -> Type) (a : Type) :=
    Pure : a -> FreeA f a
  | MkAp : forall b, f (b -> a) -> FreeA f b -> FreeA f a.

Arguments Pure {f} {a}.
Arguments MkAp {f} {a} {b}.

Fixpoint FreeA_map {A B : Type} `{Functor F}
           (g : (A -> B)) (a : FreeA F A) : FreeA F B :=
  match a with
  | Pure x   => Pure (g x)
  | MkAp h x => MkAp (fmap (fun k : _ -> A => g \o k) h) x  
  end.

Program Instance FreeA_Functor (F : Type -> Type)
  `{Functor F} : Functor (FreeA F) := {
  fmap := fun _ _ f x => FreeA_map f x
}.

Import FunctorLaws.

Lemma fmap_rewrite_compose {A B C : Type} `{Functor F} :
  forall (f : B -> C) (g : A -> B) (x : F A), 
    fmap f (fmap g x) = (fmap f \o fmap g) x.
Proof.
  intros f g x.
  reflexivity.
Qed.

Program Instance FreeA_FunctorLaws `{FunctorLaws F} : FunctorLaws (FreeA F).
(* Theorem FreeA_Functor_law1 {A : Type} *)
(*         `{Functor F} `{FunctorLaws F} : *)
(*   forall (x : FreeA F A), fmap id x = id x. *)
Obligation 1.
Proof.
extensionality x.
induction x.
- reflexivity.
- simpl.
  rewrite fmap_id.
  reflexivity.
Qed.
Obligation 2.
extensionality x.
induction x.
- reflexivity.
- simpl in *.
  f_equal.
  rewrite fmap_rewrite_compose.
  rewrite fmap_comp.
  f_equal.
Qed.

Require Coq.Program.Wf.

Fixpoint FreeA_depth {A : Type} `{Functor F}
         (x : FreeA F A) : nat :=
  match x with
  | Pure a   => O
  | MkAp _ y => S (FreeA_depth y)
  end.

Lemma FreeA_fmap_preserves_depth {A B : Type} `{Functor F} :
  forall (x : FreeA F A) (f : A -> B),
  FreeA_depth (FreeA_map f x) = FreeA_depth x.
Proof.
  intros x f.
  simpl.
  induction x; reflexivity.
Qed.

From Equations Require Import Equations.

Equations FreeA_ap {A B : Type} `{Functor F}
         (k : FreeA F (A -> B)) (y : FreeA F A) : FreeA F B by wf (FreeA_depth k) :=
FreeA_ap (Pure g) y := g <$> y;
FreeA_ap (MkAp h x) y := MkAp (fmap uncurry h) (FreeA_ap (fmap pair x) y).
Obligation 1.
Proof.
  simpl.
  rewrite FreeA_fmap_preserves_depth.
  auto.
Defined.
Transparent FreeA_ap_unfold.

(* Program Fixpoint FreeA_ap {A B : Type} `{FF: Functor F} *)
(*          (k : FreeA F (A -> B)) (y : FreeA F A) {measure (FreeA_depth k)} : FreeA F B := *)
(*   match k with *)
(*   | Pure g => g <$> y *)
(*   | MkAp h x => MkAp (fmap uncurry h) (FreeA_ap (fmap pair x) y) *)
(*   end. *)
(* Obligation 1. *)
(* Proof. *)
(*   simpl. *)
(*   rewrite FreeA_fmap_preserves_depth. *)
(*   auto. *)
(* Qed. *)

Program Instance FreeA_Applicative
  `{Functor F} : Applicative (FreeA F) := {
  pure _ x := Pure x;
  ap _ _ k y := FreeA_ap k y
}.

Import ApplicativeLaws.

Program Instance FreeA_ApplicativeLaws
  `{FunctorLaws F} :
  ApplicativeLaws (FreeA F).
Obligation 1.
extensionality y.
induction y.
- reflexivity.
- rewrite FreeA_ap_unfold_eq.
  unfold FreeA_ap_unfold.
  rewrite fmap_id.
  reflexivity.
Obligation 2.




