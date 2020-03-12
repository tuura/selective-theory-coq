Require Import Hask.Prelude.
Require Import FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

Class Functor (F : Set -> Set) : Set := {
  fmap : forall {A B : Set}, (A -> B) -> F A -> F B
}.

Arguments fmap {F _ A B} f x.

Infix "<$>" := fmap (at level 28, left associativity, only parsing).
Infix "<$[ M ]>" :=
  (@fmap M _ _ _) (at level 28, left associativity, only parsing).
(* Notation "x <$ m" := *)
(*   (fmap (const x) m) (at level 28, left associativity, only parsing). *)
(* Notation "x <&> f" := *)
(*   (fmap f x) (at level 28, left associativity, only parsing). *)

Notation "fmap[ M ]" := (@fmap M _ _ _) (at level 9).
(* Notation "fmap[ M N ]" := (@fmap (fun X => M (N X)) _ _ _) (at level 9). *)
(* Notation "fmap[ M N O ]" := *)
(*   (@fmap (fun X => M (N (O X))) _ _ _) (at level 9). *)

Definition Env (A : Set) := fun (B : Set) => A -> B.

Global Instance Env_Functor (A : Set) : Functor (Env A) := {
  fmap := fun A B f g => f ∘ g
}.

Module FunctorLaws.

(* Functors preserve extensional equality for the applied function. *)
(*    This is needed to perform setoid rewriting within the function *)
(*    passed to a functor. *)
Add Parametric Morphism {A B : Set} {F : Set -> Set} (HF : Functor F) :
  (fun f => @fmap F _ A B f)
  with signature (pointwise_relation _ eq ==> eq ==> eq)
    as mul_isomorphism.
Proof.
  intros.
  f_equal.
  extensionality e.
  now subst.
Qed.

Class FunctorLaws (F : Set -> Set) {HF : Functor F} := {
  fmap_id   : forall A : Set, fmap (@id A) = id;
  fmap_comp : forall (A B C : Set) (f : B -> C) (g : A -> B),
    fmap f ∘ fmap g = fmap (f ∘ g)
}.

Corollary fmap_id_x {F : Set -> Set} {HF : Functor F} {HFL : FunctorLaws F} :
  forall (a : Set) x, fmap (@id a) x = x.
Proof.
  intros.
  rewrite fmap_id.
  reflexivity.
Qed.

Corollary fmap_comp_x {F : Set -> Set} {HF : Functor F} {HFL : FunctorLaws F} :
  forall (A B C : Set) (f : B -> C) (g : A -> B) x,
  fmap f (fmap g x) = fmap (fun y => f (g y)) x.
Proof.
  intros.
  replace (fun y : A => f (g y)) with (f ∘ g).
    rewrite <- fmap_comp.
    reflexivity.
  reflexivity.
Qed.

Ltac functor_laws :=
  repeat
    match goal with
    | [ |- context[fmap[?F] id] ] =>
      rewrite fmap_id
    | [ |- context[fmap[?F] _ (fmap[?F] _ _)] ] =>
      rewrite fmap_comp_x
    | [ |- context[fmap[?F] id] ] =>
      setoid_rewrite fmap_id
    | [ |- context[fmap[?F] _ (fmap[?F] _ _)] ] =>
      setoid_rewrite fmap_comp_x
    end; auto.

End FunctorLaws.
