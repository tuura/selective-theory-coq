Require Import Hask.Ltac.
(* Require Import Control.Iso. *)
Require Import Coq.Program.Basics.
Local Open Scope program_scope.
Require Import Hask.Prelude.
Require Import Data.Either.
Require Import Data.Monoid.
Require Import Hask.Data.Functor.
Require Import Hask.Data.Functor.Const.
Require Import Hask.Control.Applicative.

Set Universe Polymorphism.
Generalizable All Variables.

Reserved Notation "f <*? g" (at level 28, left associativity).
(* Notation "fmap[ M ]" := (@fmap M _ _ _) (at level 9). *)

Class Selective (f : Type -> Type) := {
  is_applicative :> Applicative f;

  select   : forall a b : Type, f (a + b)%type -> f (a -> b) -> f b
}.

Arguments select {f _ _ _} _ x.

Infix "<*?" := select (at level 28, left associativity).
Infix "<*[ M ]?" :=
  (@select M _ _ _) (at level 28, left associativity).


(* apS :: Selective f => f (a -> b) -> f a -> f b *)
(* apS f x = select (Left <$> f) (flip ($) <$> x) *)
Definition apS `{Selective f} {A B : Type}
           (t : f (A -> B)) (x : f A) : f B :=
  select (Left <$> t) ((fun y f => f y) <$> x).

(* selectA :: Applicative f => f (Either a b) -> f (a -> b) -> f b *)
(* selectA x y = (\e f -> either f id e) <$> x <*> y *)
Definition selectA `{Applicative f} {A B : Type}
           (x : f (A + B)%type) (y : f (A -> B)) : f B :=
  (fun e f => either f id e) <$> x <*> y.

Module SelectiveParametricity.

Import FunctorLaws.

Theorem free_theorem_1 :
  forall (A B C : Type) `{Selective F} (f : B -> C) (x : F (A + B)%type) (y : F (A -> B)),
    f <$> (select x y) =
    select (fmap[Either A] f <$> x)
           (fmap[Env A] f <$> y).
Admitted.

(* The following lemma is a specialisation of the first free theorem *)
(* in the case when the first argument of select is 'Left' *)
(* Many implicit arguments must be provided explicitly in order for the *)
(* lemma to typecheck properly *)
Corollary free_theorem_1_left :
  forall (X A C : Type) (F : Type -> Type)
    (H : Selective F) (FL : FunctorLaws F)
    (f : X -> C)
    (x : F A)
    (y : F (A -> X)),
    @fmap F _ _ _ f (@select F H _ _ (@Left A X <$> x) y) =
    @select F H _ _ ((@Left A C) <$[F]> x)
            ((fmap[Env A] f) <$[F]> y).
Proof.
  intros X A C F H HFL f x y.
  rewrite free_theorem_1.
  rewrite fmap_comp_x.
  f_equal.
Qed.

Theorem free_theorem_2 `{Selective F} :
  forall (A B C : Type) (f : A -> C) (x : F (A + B)%type) (y : F (C -> B)),
    select (fmap (mapLeft f) x) y = select x ((fun g : C -> B => g ∘ f) <$> y).
Admitted.

Check rev_f_ap.

Theorem free_theorem_3 `{Selective F} :
  forall (A B C : Type) (f : C -> A -> B)
                   (x : F (A + B)%type)
                   (y : F C),
    x <*? (f <$> y) = (mapLeft (flip f) <$> x) <*? ((@rev_f_ap _ _) <$> y).
Admitted.


Ltac apply_free_theorems :=
  repeat
    match goal with
    | [ |- context[_ <$> (select _ _)] ] =>
      rewrite free_theorem_1
    end; auto.

End SelectiveParametricity.

Module SelectiveLaws.

Include ApplicativeLaws.

Definition law3_f {A B C : Type}
           (x : B + C) : B + (A + C) := Right <$> x.

Definition law3_g {A B C : Type}
           (y : A + (B -> C)) : B -> A * B + C :=
  fun a => Either_bimap (fun p => pair p a) (fun f => f a) y.

Definition law3_h  {A B C : Type}
           (f : A -> B -> C) : A * B -> C :=
  fun p => match p with
           | pair x y => f x y
           end.

Class SelectiveLaws (F : Type -> Type) `{Selective F} := {
  has_applicative_laws :> ApplicativeLaws F;

  select_identity : forall (A : Type) (x : F (A + A)%type),
      x <*? (pure id) = either id id <$> x;
  select_distr    : forall (A B : Type) (x : (A + B)%type) (y : F (A -> B)) (z : F (A -> B)),
                    pure x <*? (y *> z) = (pure x <*? y) *> (pure x <*? z);
  select_assoc    : forall (A B C : Type) (x : F ((B + C)%type)) (y : F (Either A (B -> C)))
                                          (z : F (A -> B -> C)),
                     x <*? (y <*? z) = (law3_f <$> x) <*? (law3_g <$> y) <*? (law3_h <$> z)
}.

End SelectiveLaws.
