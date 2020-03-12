Require Import Hask.Ltac.
Require Import Hask.Data.Functor.
Require Import FunctionalExtensionality.

Generalizable All Variables.
Set Universe Polymorphism.

Polymorphic Class Contravariant (f : Set -> Set) := {
  contramap : forall {a b : Set}, (a -> b) -> f b -> f a
}.

Arguments contramap {f _ a b} _ x.

Infix ">$<" := contramap (at level 28, left associativity, only parsing).
Notation "x >&< f" :=
  (contramap f x) (at level 28, left associativity, only parsing).

Notation "contramap[ M ]  f" := (@contramap M _ _ _ f) (at level 9).
Notation "contramap[ M N ]  f" :=
  (@contramap (fun X => M (N X)) _ _ _ f) (at level 9).
Notation "contramap[ M N O ]  f" :=
  (@contramap (fun X => M (N (O X))) _ _ _ f) (at level 9).

Definition coerce `{Functor f} `{Contravariant f} {a b} : f a -> f b :=
  fmap (False_rect _) \o contramap (False_rect _).

Instance Contravariant_Compose `{Functor F} `{Contravariant G} :
  Contravariant (F \o G) :=
{ contramap := fun A B => @fmap F _ (G B) (G A) \o @contramap G _ A B
}.

Module ContravariantLaws.

Import FunctorLaws.

Polymorphic Class ContravariantLaws (f : Set -> Set) `{Contravariant f} := {
  contramap_id   : forall a : Set, contramap (@id a) = id;
  contramap_comp : forall (a b c : Set) (f : b -> c) (g : a -> b),
    contramap g \o contramap f = contramap (f \o g)
}.

Corollary contramap_id_x `{ContravariantLaws f} :
  forall (a : Set) x, contramap (@id a) x = x.
Proof. intros; rewrite contramap_id. auto. Qed.

Corollary contramap_comp_x `{ContravariantLaws F} :
  forall (a b c : Set) (f : b -> c) (g : a -> b) x,
  contramap g (contramap f x) = contramap (fun y => f (g y)) x.
Proof.
  intros.
  replace (fun y : a => f (g y)) with (f \o g).
    rewrite <- contramap_comp.
    reflexivity.
  reflexivity.
Qed.

End ContravariantLaws.
