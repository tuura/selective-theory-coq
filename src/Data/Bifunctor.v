Require Import Hask.Ltac.
Require Import FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Program.Basics.
Require Import Data.Functor.
Local Open Scope program_scope.

Set Universe Polymorphism.
Generalizable All Variables.

Polymorphic Class Bifunctor (F : Set -> Set -> Set) : Set := {
  bimap : forall {A B C D : Set}, (A -> C) -> (B -> D) -> F A B -> F C D
}.

Arguments bimap {F _ A B C D} f g x.

Module BifunctorLaws.

(* Lemma bimap_fmap_fuse_right : *)
(*   forall (A B C D X : Set) (F : Set -> Set -> Set) *)
(*   `(Bifunctor F) `(Functor (F X)) *)
(*   (f : A -> C) (g : B -> D) (h : X -> B), *)
(*   bimap f g ∘ fmap[ F X ] h = bimap f (g ∘ h). *)
(* Proof. *)
(*   intros A B C D X f g h. *)
(*   extensionality x. *)
(*   now destruct x. *)
(* Qed. *)

Lemma Either_bimap_mapLeft_fuse :
  forall (A B C D X : Set)
         (f : B -> C) (g : B -> D) (h : C -> X),
  mapLeft h ∘ Either_bimap f g = Either_bimap (h ∘ f) g.
Proof.
  intros A B C D X f g h.
  extensionality x.
  now destruct x.
Qed.

(* (* Bifunctors preserve extensional equality for the applied functions. *)
(*    This is needed to perform setoid rewriting within the function *)
(*    passed to a bifunctor. *) *)
(* Add Parametric Morphism {A B} `{Functor F} : (@fmap F _ A B) *)
(*   with signature (pointwise_relation _ eq ==> eq ==> eq) *)
(*     as mul_isomorphism. *)
(* Proof. *)
(*   intros. *)
(*   f_equal. *)
(*   extensionality e. *)
(*   apply H0. *)
(* Qed. *)

(* Class FunctorLaws (f : Set -> Set) `{Functor f} := { *)
(*   fmap_id   : forall a : Set, fmap (@id a) = id; *)
(*   fmap_comp : forall (a b c : Set) (f : b -> c) (g : a -> b), *)
(*     fmap f \o fmap g = fmap (f \o g) *)
(* }. *)

(* Corollary fmap_id_x `{FunctorLaws f} : forall (a : Set) x, fmap (@id a) x = x. *)
(* Proof. *)
(*   intros. *)
(*   rewrite fmap_id. *)
(*   reflexivity. *)
(* Qed. *)

(* Corollary fmap_comp_x `{FunctorLaws F} : *)
(*   forall (a b c : Set) (f : b -> c) (g : a -> b) x, *)
(*   fmap f (fmap g x) = fmap (fun y => f (g y)) x. *)
(* Proof. *)
(*   intros. *)
(*   replace (fun y : a => f (g y)) with (f \o g). *)
(*     rewrite <- fmap_comp. *)
(*     reflexivity. *)
(*   reflexivity. *)
(* Qed. *)

(* End FunctorLaws. *)
