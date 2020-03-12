Require Import Hask.Prelude.
Require Import Data.Either.
Require Import Data.Monoid.
Require Import Data.Functor.
Require Import Control.Applicative.
Require Import Control.Selective.

Inductive Over (C A : Set) := MkOver : C -> Over C A.

Arguments MkOver {C} {A}.

Instance Over_Functor (C : Set) : Functor (Over C) := {
  fmap := fun a b f x => match x with
                         | MkOver c => MkOver c
                         end
}.

Instance Over_Applicative (C : Set) {HM : Monoid C} : Applicative (Over C) :=
  { is_functor := Over_Functor C
  ; pure := fun _ _  => @MkOver C _ mempty
  ; ap   := fun _ _ f x => match f, x with
                           | MkOver g, MkOver y => MkOver (mappend g y)
                           end
}.

Instance Over_Selective (C : Set) {HM : Monoid C} : Selective (Over C) :=
  { is_applicative := Over_Applicative C
  ; select := fun _ _ => selectA
  }.

(******************** Selective laws *****************************)
Theorem over_selective_law1_identity
  {A M : Set} {HM : Monoid M} {x : Over M (Either A A)} :
  x <*? (pure id) = either id id <$> x.
Proof.
  destruct x.
  simpl.
  rewrite mon_right_id.
  reflexivity.
Qed.

Theorem over_selective_law2_distr
  {A B M : Set} {HM : Monoid M}
  (x : (Either A B))
  (y : Over M (A -> B))
  (z : Over M (A -> B)) :
  pure x <*? (y *> z) = (pure x <*? y) *> (pure x <*? z).
Proof.
  destruct x;
  destruct y;
  destruct z;
  cbn;
  now repeat rewrite mon_left_id.
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

Theorem over_selective_law3_assoc
  {A B C M : Set} {HM : Monoid M}
  (x : Over M (B + C))
  (y : Over M (A + (B -> C)))
  (z : Over M (A -> B -> C)) :
  x <*? (y <*? z) = (law3_f <$> x) <*? (law3_g <$> y) <*? (law3_h <$> z).
Proof.
  destruct x.
  destruct y.
  destruct z.
  simpl.
  rewrite mon_assoc.
  reflexivity.
Qed.

(******************** Selective theorems *****************************)

(* -- Apply a pure function to the result *)
(* f <$> select x y = select (fmap f <$> x) (fmap f <$> y) *)
Theorem over_selective_theorem1
  {A B C M : Set} {HM : Monoid M}
  (f : A -> C) (x : Over M (B + A)) (y : Over M (B -> A)) :
  f <$> select x y = select (fmap f <$> x) ((fun g => f ∘ g) <$> y).
Proof.
  destruct x.
  destruct y.
  simpl.
  reflexivity.
Qed.
(* -- Apply a pure function to the Left case of the first argument *)
(* select (first f <$> x) y = select x ((. f) <$> y) *)
Theorem over_selective_theorem2
  {A B C M : Set} {HM : Monoid M}
  (f : A -> B) (x : Over M (A + C)) (y : Over M (B -> C)) :
  select (mapLeft f <$> x) y = select x ((fun g : _ -> _ => g ∘ f) <$> y).
Proof.
  destruct x.
  destruct y.
  simpl.
  reflexivity.
Qed.
(* -- Apply a pure function to the second argument *)
(* select x (f <$> y) = select (first (flip f) <$> x) (flip ($) <$> y) *)
Theorem over_selective_theorem3
  {A B C M : Set} {HM : Monoid M}
  (f : A -> B -> C) (x : Over M (B + C)) (y : Over M A) :
  select x (f <$> y) = select (mapLeft (flip f) <$> x) ((fun y f => f y) <$> y).
Proof.
  destruct x.
  destruct y.
  simpl.
  reflexivity.
Qed.
(* -- Generalised identity *)
(* x <*? pure y = either y id <$> x *)
Theorem over_selective_theorem4
  {A B M : Set} {HM : Monoid M}
  (x : Over M (A + B)) (y : A -> B) :
  x <*? pure y = either y id <$> x.
Proof.
  destruct x.
  simpl.
  rewrite mon_right_id.
  reflexivity.
Qed.
(* -- Selective apply *)
(* (<*>) = apS *)
Theorem over_selective_theorem5
  {A B M : Set} {HM : Monoid M}
  (f : Over M (A -> B)) (x : Over M A) :
  f <*> x = apS f x.
Proof.
  destruct x.
  destruct f.
  simpl.
  reflexivity.
Qed.
(* -- Interchange *)
(* x *> (y <*? z) = (x *> y) <*? z *)
Theorem over_selective_theorem6
  {A B C M : Set} {HM : Monoid M}
  (x : Over M A) (y : Over M (B + C)) (z : Over M (B -> C)) :
  x *> (y <*? z) = (x *> y) <*? z.
Proof.
  destruct x.
  destruct y.
  destruct z.
  simpl.
  rewrite mon_assoc.
  reflexivity.
Qed.
