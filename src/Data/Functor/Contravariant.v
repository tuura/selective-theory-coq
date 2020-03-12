Require Import Hask.Prelude.
Require Import Hask.Data.Functor.
Require Import FunctionalExtensionality.

Class Contravariant (F : Set -> Set) := {
  contramap : forall {A B : Set}, (A -> B) -> F B -> F A
}.

Arguments contramap {F _ A B} _ x.

Infix ">$<" := contramap (at level 28, left associativity, only parsing).
Notation "x >&< f" :=
  (contramap f x) (at level 28, left associativity, only parsing).

Notation "contramap[ M ]  f" := (@contramap M _ _ _ f) (at level 9).
Notation "contramap[ M N ]  f" :=
  (@contramap (fun X => M (N X)) _ _ _ f) (at level 9).
Notation "contramap[ M N O ]  f" :=
  (@contramap (fun X => M (N (O X))) _ _ _ f) (at level 9).

Definition coerce
  {F : Set -> Set} {HF : Functor F} {HCF : Contravariant F}
  {A B : Set} : F A -> F B :=
  fmap (False_rect _) ∘ contramap (False_rect _).

Module ContravariantLaws.

 Import FunctorLaws.

Class ContravariantLaws (F : Set -> Set) {HCF : Contravariant F} := {
  contramap_id   : forall a : Set, contramap (@id a) = id;
  contramap_comp : forall (a b c : Set) (f : b -> c) (g : a -> b),
    contramap g ∘ contramap f = contramap (f ∘ g)
}.

End ContravariantLaws.
