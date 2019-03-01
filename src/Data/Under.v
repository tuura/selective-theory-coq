Require Import Coq.Program.Basics.
Require Import Hask.Prelude.
Require Import Data.Either.
Require Import Data.Monoid.
Require Import Data.Functor.
Require Import Control.Applicative.
Require Import Control.Selective.

Inductive Under (c a : Type) := MkUnder : c -> Under c a.

Arguments MkUnder {c} {a}.

Program Instance Under_Functor (c : Type) : Functor (Under c) := {
  fmap := fun a b f x => match x with
                         | MkUnder c => MkUnder c
                         end
}.

Program Instance Under_Applicative (c : Type) `{Monoid c} : Applicative (Under c) :=
  { is_functor := Under_Functor c
  ; pure := fun _ _  => @MkUnder c _ mempty
  ; ap   := fun _ _ f x => match f, x with
                           | MkUnder g, MkUnder y => MkUnder (mappend g y)
                           end
}.

Program Instance Under_Selective (c : Type) `{Monoid c}: Selective (Under c) :=
  { is_applicative := Under_Applicative c
    ; select := fun _ _ f _ => match f with
                               | MkUnder x => MkUnder x
                               end
  }.

(******************** Selective laws *****************************)
Theorem under_selective_law1_identity
  {A M : Type} `{Monoid M} {x : Under M (Either A A)} :
  x <*? (pure id) = either id id <$> x.
Proof.
  destruct x.
  simpl.
  reflexivity.
Qed.

Theorem under_selective_law2_distr
  {A B M : Type} `{Monoid M}
  (x : (Either A B))
  (y : Under M (A -> B))
  (z : Under M (A -> B)) :
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

Theorem under_selective_law3_assoc
  {A B C M : Type} `{Monoid M}
  (x : Under M (B + C))
  (y : Under M (A + (B -> C)))
  (z : Under M (A -> B -> C)) :
  x <*? (y <*? z) = (law3_f <$> x) <*? (law3_g <$> y) <*? (law3_h <$> z).
Proof.
  destruct x.
  destruct y.
  destruct z.
  simpl.
  reflexivity.
Qed.

(******************** Selective theorems *****************************)

(* -- Apply a pure function to the result *)
(* f <$> select x y = select (fmap f <$> x) (fmap f <$> y) *)
Theorem under_selective_theorem1
  {A B C M : Type} `{Monoid M}
  (f : A -> C) (x : Under M (B + A)) (y : Under M (B -> A)) :
  f <$> select x y = select (fmap f <$> x) ((fun g => compose f g) <$> y).
Proof.
  destruct x.
  destruct y.
  simpl.
  reflexivity.
Qed.
(* -- Apply a pure function to the Left case of the first argument *)
(* select (first f <$> x) y = select x ((. f) <$> y) *)
Theorem under_selective_theorem2
  {A B C M : Type} `{Monoid M}
  (f : A -> B) (x : Under M (A + C)) (y : Under M (B -> C)) :
  select (mapLeft f <$> x) y = select x ((fun g => compose g f) <$> y).
Proof.
  destruct x.
  destruct y.
  simpl.
  reflexivity.
Qed.
(* -- Apply a pure function to the second argument *)
(* select x (f <$> y) = select (first (flip f) <$> x) (flip ($) <$> y) *)
Theorem under_selective_theorem3
  {A B C M : Type} `{Monoid M}
  (f : A -> B -> C) (x : Under M (B + C)) (y : Under M A) :
  select x (f <$> y) = select (mapLeft (flip f) <$> x) ((fun y f => f y) <$> y).
Proof.
  destruct x.
  destruct y.
  simpl.
  reflexivity.
Qed.
(* -- Generalised identity *)
(* x <*? pure y = either y id <$> x *)
Theorem under_selective_theorem4
  {A B M : Type} `{Monoid M}
  (x : Under M (A + B)) (y : A -> B) :
  x <*? pure y = either y id <$> x.
Proof.
  destruct x.
  simpl.
  reflexivity.
Qed.
(* -- Interchange *)
(* x *> (y <*? z) = (x *> y) <*? z *)
Theorem under_selective_theorem6
  {A B C M : Type} `{Monoid M}
  (x : Under M A) (y : Under M (B + C)) (z : Under M (B -> C)) :
  x *> (y <*? z) = (x *> y) <*? z.
Proof.
  destruct x.
  destruct y.
  destruct z.
  simpl.
  reflexivity.
Qed.
