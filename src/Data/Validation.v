Require Import Coq.Program.Basics.
Require Import Hask.Prelude.
Require Import Data.Either.
Require Import Data.Monoid.
Require Import Data.Functor.
Require Import Control.Applicative.
Require Import Control.Selective.

Inductive Validation (e a : Type) :=
    Failure : e -> Validation e a
  | Success : a -> Validation e a.

Arguments Failure {e} {a} _.
Arguments Success {e} {a} _.

Program Instance Validation_Functor (c : Type) : Functor (Validation c) := {
  fmap := fun a b f x => match x with
                         | Failure e => Failure e
                         | Success a => Success (f a)
                         end
}.

Program Instance Validation_Applicative (c : Type) `{Monoid c} : Applicative (Validation c) :=
  { is_functor := Validation_Functor c
  ; pure := fun _ x => Success x
  ; ap   := fun _ _ f x =>
    match f, x with
    | Failure e1, Failure e2 => Failure (mappend e1 e2)
    | Failure e1, Success _  => Failure e1
    | Success _ , Failure e2 => Failure e2
    | Success f , Success a  => Success (f a)
    end
}.

Program Instance Validation_Selective (c : Type) `{Monoid c}: Selective (Validation c) :=
  { is_applicative := Validation_Applicative c
    ; select := fun _ _ x f =>
      match x with
      | Success (Right b) => Success b
      | Success (Left  a) => (fun g => g a) <$> f
      | Failure e         => Failure e
      end
  }.

(******************** Selective laws *****************************)
Theorem validation_selective_law1_identity
  {A M : Type} `{Monoid M} {x : Validation M (Either A A)} :
  x <*? (pure id) = either id id <$> x.
Proof.
  destruct x.
  - simpl.
    reflexivity.
  - destruct s;
    simpl;
    reflexivity.
Qed.

Theorem validation_selective_law2_distr
  {A B M : Type} `{Monoid M}
  (x : (Either A B))
  (y : Validation M (A -> B))
  (z : Validation M (A -> B)) :
  pure x <*? (y *> z) = (pure x <*? y) *> (pure x <*? z).
Proof.
  destruct x;
  destruct y;
  destruct z;
  simpl;
  repeat rewrite mon_left_id;
  reflexivity.
Qed.

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

Theorem validation_selective_law3_assoc
  {A B C M : Type} `{Monoid M}
  (x : Validation M (B + C))
  (y : Validation M (A + (B -> C)))
  (z : Validation M (A -> B -> C)) :
  x <*? (y <*? z) = (law3_f <$> x) <*? (law3_g <$> y) <*? (law3_h <$> z).
Proof.
  destruct x.
  - simpl. reflexivity.
  - destruct y.
    + destruct s;
      simpl; reflexivity.
    + destruct s;
      destruct z;
      destruct s0;
      simpl; reflexivity.
Qed.
(******************** Selective theorems *****************************)

(* -- Apply a pure function to the result *)
(* f <$> select x y = select (fmap f <$> x) (fmap f <$> y) *)
Theorem validation_selective_theorem1
  {A B C M : Type} `{Monoid M}
  (f : A -> C) (x : Validation M (B + A)) (y : Validation M (B -> A)) :
  f <$> select x y = select (fmap f <$> x) ((fun g => compose f g) <$> y).
Proof.
  destruct x.
  - simpl. reflexivity.
  - destruct s;
    destruct y;
    simpl; reflexivity.
Qed.
(* -- Apply a pure function to the Left case of the first argument *)
(* select (first f <$> x) y = select x ((. f) <$> y) *)
Theorem validation_selective_theorem2
  {A B C M : Type} `{Monoid M}
  (f : A -> B) (x : Validation M (A + C)) (y : Validation M (B -> C)) :
  select (mapLeft f <$> x) y = select x ((fun g => compose g f) <$> y).
Proof.
  destruct x.
  - destruct y;
    simpl; reflexivity.
  - destruct y;
    destruct s;
    simpl; reflexivity.
Qed.
(* -- Apply a pure function to the second argument *)
(* select x (f <$> y) = select (first (flip f) <$> x) (flip ($) <$> y) *)
Theorem validation_selective_theorem3
  {A B C M : Type} `{Monoid M}
  (f : A -> B -> C) (x : Validation M (B + C)) (y : Validation M A) :
  select x (f <$> y) = select (mapLeft (flip f) <$> x) ((fun y f => f y) <$> y).
Proof.
  destruct x.
  - destruct y;
    simpl; reflexivity.
  - destruct y;
    destruct s; simpl; reflexivity.
Qed.
(* -- Generalised identity *)
(* x <*? pure y = either y id <$> x *)
Theorem validation_selective_theorem4
  {A B M : Type} `{Monoid M}
  (x : Validation M (A + B)) (y : A -> B) :
  x <*? pure y = either y id <$> x.
Proof.
  destruct x.
  - simpl.
    reflexivity.
  - destruct s; simpl; reflexivity.
Qed.
