Require Import Hask.Ltac.
Require Import Data.Either.
Require Import Data.Monoid.
Require Import Hask.Data.Functor.
Require Import Hask.Data.Functor.Const.
Require Import Hask.Control.Applicative.

Generalizable All Variables.

Reserved Notation "f <*? g" (at level 28, left associativity).

Class Selective (f : Type -> Type) := {
  is_applicative :> Applicative f;

  select   : forall a b : Type, f (Either a b) -> f (a -> b) -> f b
}.

Arguments select {f _ _ _} _ x.

Infix "<*?" := select (at level 28, left associativity, only parsing).

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
