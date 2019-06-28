Require Import Hask.Ltac.
Require Import Coq.Program.Basics.
Require Import Hask.Prelude.
Require Import Data.Either.
Require Import Data.Monoid.
Require Import Hask.Data.Functor.
Require Import Hask.Control.Applicative.

Generalizable All Variables.

Reserved Notation "f <*? g" (at level 28, left associativity).

Class Selective (f : Type -> Type) := {
  is_applicative :> Applicative f;

  select   : forall a b : Type, f (Either a b) -> f (a -> b) -> f b
}.

Arguments select {f _ _ _} _ x.

Infix "<*?" := select (at level 28, left associativity).

(* apS :: Selective f => f (a -> b) -> f a -> f b *)
(* apS f x = select (Left <$> f) (flip ($) <$> x) *)
Definition apS `{Selective f} {A B : Type}
           (t : f (A -> B)) (x : f A) : f B :=
  select (Left <$> t) ((fun y f => f y) <$> x).

(* selectA :: Applicative f => f (Either a b) -> f (a -> b) -> f b *)
(* selectA x y = (\e f -> either f id e) <$> x <*> y *)
Definition selectA `{Applicative f} {A B : Type}
           (x : f (Either A B)) (y : f (A -> B)) : f B :=
  (fun e f => either f id e) <$> x <*> y.

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

  select_identity : forall (A : Type) (x : F (Either A A)), x <*? (pure id) = either id id <$> x;
  select_distr    : forall (A B : Type) (x : Either A B) (y : F (A -> B)) (z : F (A -> B)),
                    pure x <*? (y *> z) = (pure x <*? y) *> (pure x <*? z);
  select_assoc    : forall (A B C : Type) (x : F (Either B C)) (y : F (Either A (B -> C)))
                                          (z : F (A -> B -> C)),
                     x <*? (y <*? z) = (law3_f <$> x) <*? (law3_g <$> y) <*? (law3_h <$> z)
}.

End SelectiveLaws.
