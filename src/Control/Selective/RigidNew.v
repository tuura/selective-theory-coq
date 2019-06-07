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
Require Import Omega.
From Equations Require Import Equations.

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

(* Inductive Select (f : Type -> Type) (a : Type) := *)
(*     Pure   : a -> Select f a *)
(*   | MkSelect : forall b, Select f (b + a) -> f (b -> a) -> Select f a. *)
Inductive Select (F : Type -> Type) (A : Type) :=
    Pure   : A -> Select F A
  | MkSelect : forall B C, (C -> ((B -> A) + A)) -> Select F C -> F B -> Select F A.

Arguments Pure {F} {A}.
Arguments MkSelect {F} {A} {B} {C}.

(******************************************************************************)
(************************ Functor and FunctorLaws *****************************)
(******************************************************************************)
Equations Select_map {A B : Type} `{Functor F}
           (f : A -> B) (x : Select F A) : Select F B :=
Select_map f (Pure a) => Pure (f a);
Select_map f (MkSelect g x y) =>
  MkSelect (fun x => Either_bimap (fun k => f \o k) f (g x)) x y.

Program Instance Select_Functor (F : Type -> Type)
  `{Functor F} : Functor (Select F) := {
  fmap := fun _ _ f x => Select_map f x
}.

(* Auxiliary lemmas for proving Functor laws *)
Definition id_f {A : Type} (x : A) := x.

Lemma id_x_is_x {A : Type}:
  forall (x : A), id x = x.
Proof. intros x. reflexivity. Qed.

Lemma id_comp {A B : Type}:
  forall (f : A -> B), (id \o f) = f.
Proof.
  intros f.
  extensionality x.
  now unfold comp.
Qed.

Import FunctorLaws.

Lemma fmap_rewrite_compose {A B C : Type} `{Functor F} :
  forall (f : B -> C) (g : A -> B) (x : F A),
    fmap f (fmap g x) = (fmap f \o fmap g) x.
Proof.
  intros f g x.
  reflexivity.
Qed.

Program Instance Select_FunctorLaws `{FunctorLaws F} : FunctorLaws (Select F).
(* Theorem Select_Functor_law1 {A : Type} *)
(*         `{Functor F} `{FunctorLaws F} : *)
(*   forall (x : Select F A), fmap id x = id x. *)
Obligation 1.
unfold id.
extensionality x.
destruct x.
- rewrite Select_map_equation_1. reflexivity.
- rewrite Select_map_equation_2.
  f_equal.
  remember (fun k : B -> a => (fun x1 : a => x1) \o k)  as t.
  assert ((fun x1 : a => x1) = id).
  { reflexivity. }
  rewrite H1 in *.
  rewrite Heqt.
  extensionality y.
  unfold Either_bimap.
  destruct (s y).
  + now rewrite id_comp.
  + now rewrite id_x_is_x.
Qed.
(* Theorem Select_Functor_law2 {A B C : Type} *)
(*         `{Functor F} `{FunctorLaws F} : *)
(*   forall (f : B -> C) (g : A -> B) (x : Select F A), *)
(*   ((Select_map f) \o (Select_map g)) x = Select_map (f \o g) x. *)
Obligation 2.
extensionality x.
simpl.
destruct x.
- trivial.
- repeat rewrite Select_map_equation_2.
  f_equal.
  extensionality x0.
  unfold Either_bimap.
  destruct (s x0); reflexivity.
Qed.

(* (******************************************************************************) *)
(* (************************ Selective               *****************************) *)
(* (******************************************************************************) *)

(* This is a halper function used in the Select_select definition *) 
Definition h {A B C D E F: Type}
           (f : A -> ((B -> C) + C))
           (g : D -> ((E -> B) + B))
           (a : A) : Either (D -> Either (E -> C) C) (Either F C) :=
  match f a with
  | inr r => Right (Right r)
  | inl l => Left  (Either_bimap (fun k => l \o k) l \o g) 
  end.

Fixpoint Select_select {A B C : Type} `{Functor F}
          (f : A -> ((B -> C) + C))
          (x : Select F A)
          (a : Select F B) : Select F C :=
  match a with
  | Pure y => (either (fun k => k y) id \o f) <$> x
  | MkSelect g y z => MkSelect id (Select_select (h f g) x y) z
  end.

Definition Select_ap {A B : Type} `{Functor F}
           (f : Select F (A -> B)) (x : Select F A) : Select F B :=
  Select_select Left f x.

Program Instance Select_Applicative
        (F : Type -> Type) `{Functor F} : Applicative (Select F) :=
  { is_functor := Select_Functor F
  ; pure _ x := Pure x
  ; ap _ _ f x := Select_ap f x
}.

Import ApplicativeLaws.

(* (forall (F : Type -> Type) (H : Functor F), *)
(*  FunctorLaws F -> forall a : Type, ap[ Select F] ((pure[ Select F]) id) = id). *)
(* pure id <*> v = v   *)

Polymorphic Definition pid {A : Type} (a : A) := a.

Theorem Select_Applicative_law1
        `{FunctorLaws F} :
  forall (A : Type) (x : Select F A),
  Select_ap (Pure id) x = id x.
Proof.
  unfold Select_ap.
  Set Printing Universes.
  induction x.

