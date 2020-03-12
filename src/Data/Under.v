Require Import Hask.Prelude.
Require Import Data.Either.
Require Import Data.Monoid.
Require Import Data.Functor.
Require Import Control.Applicative.
Require Import Control.Selective.

Inductive Under (C A : Set) := MkUnder : C -> Under C A.

Arguments MkUnder {_ _}.

Instance Under_Functor (C : Set) : Functor (Under C) := {
  fmap := fun a b f x => match x with
                         | MkUnder c => MkUnder c
                         end
}.

Instance Under_Applicative (M : Set) {HM : Monoid M} : Applicative (Under M) :=
  { is_functor := Under_Functor M
  ; pure := fun _ _  => @MkUnder M _ mempty
  ; ap   := fun _ _ f x => match f, x with
                           | MkUnder g, MkUnder y => MkUnder (mappend g y)
                           end
}.

Program Instance Under_Selective (M : Set) {HM : Monoid M}: Selective (Under M) :=
  { is_applicative := Under_Applicative M
    ; select := fun _ _ f _ => match f with
                               | MkUnder x => MkUnder x
                               end
  }.

(******************** Selective laws *****************************)
Theorem under_selective_law1_identity
  {A M : Set} {HM : Monoid M} {x : Under M (Either A A)} :
  x <*? (pure id) = either id id <$> x.
Proof.
  destruct x.
  simpl.
  reflexivity.
Qed.

Theorem under_selective_law2_distr
  {A B M : Set} {HM : Monoid M}
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

Definition law3_f {A B C : Set}
           (x : B + C) : B + (A + C) := Right <$> x.

Definition law3_g {A B C : Set}
           (y : A + (B -> C)) : B -> A * B + C :=
  fun a => Either_bimap (fun p => pair p a) (fun f => f a) y.

Definition law3_h  {A B C : Set}
           (f : A -> B -> C) : A * B -> C :=
  fun p => match p with
           | pair x y => f x y
           end.

Theorem under_selective_law3_assoc
  {A B C M : Set} {HM : Monoid M}
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
  {A B C M : Set} {HM : Monoid M}
  (f : A -> C) (x : Under M (B + A)) (y : Under M (B -> A)) :
  f <$> select x y = select (fmap f <$> x) ((fun g => f ∘ g) <$> y).
Proof.
  destruct x.
  destruct y.
  simpl.
  reflexivity.
Qed.
(* -- Apply a pure function to the Left case of the first argument *)
(* select (first f <$> x) y = select x ((. f) <$> y) *)
Theorem under_selective_theorem2
  {A B C M : Set} {HM : Monoid M}
  (f : A -> B) (x : Under M (A + C)) (y : Under M (B -> C)) :
  select (mapLeft f <$> x) y = select x ((fun g : _ -> _ => g ∘ f) <$> y).
Proof.
  destruct x.
  destruct y.
  simpl.
  reflexivity.
Qed.
(* -- Apply a pure function to the second argument *)
(* select x (f <$> y) = select (first (flip f) <$> x) (flip ($) <$> y) *)
Theorem under_selective_theorem3
  {A B C M : Set} {HM : Monoid M}
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
  {A B M : Set} {HM : Monoid M}
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
  {A B C M : Set} {HM : Monoid M}
  (x : Under M A) (y : Under M (B + C)) (z : Under M (B -> C)) :
  x *> (y <*? z) = (x *> y) <*? z.
Proof.
  destruct x.
  destruct y.
  destruct z.
  simpl.
  reflexivity.
Qed.
