Require Import Reasoning.
Require Import Hask.Prelude.
Require Import Data.Either.
Require Import Data.Monoid.
Require Import Hask.Data.Functor.
Require Import Hask.Data.Functor.Const.
Require Import Hask.Control.Applicative.

Reserved Notation "f <*? g" (at level 28, left associativity).
(* Notation "fmap[ M ]" := (@fmap M _ _ _) (at level 9). *)

Class Selective (F : Set -> Set) := {
  is_applicative :> Applicative F;

  select   : forall A B : Set, F (A + B)%type -> F (A -> B) -> F B
}.

Arguments select {F _ _ _} _ x.

Infix "<*?" := select (at level 28, left associativity).
Infix "<*[ M ]?" :=
  (@select M _ _ _) (at level 28, left associativity).


(* apS :: Selective f => f (a -> b) -> f a -> f b *)
(* apS f x = select (Left <$> f) (flip ($) <$> x) *)
Definition apS {A B : Set} {F : Set -> Set} {HS : Selective F}
           (t : F (A -> B)) (x : F A) : F B :=
  select (Left <$> t) ((fun y f => f y) <$> x).

(* selectA :: Applicative f => f (Either a b) -> f (a -> b) -> f b *)
(* selectA x y = (\e f -> either f id e) <$> x <*> y *)
Definition selectA {A B : Set} {F : Set -> Set} {HA : Applicative F}
           (x : F (A + B)%type) (y : F (A -> B)) : F B :=
  (fun e f => either f id e) <$> x <*> y.

Section SelectiveParametricity.
  Context (F : Set -> Set).
  Context (HS : Selective F).

  Import FunctorLaws.

  Axiom free_theorem :
    forall (A B C D : Set)
    (f : A -> C) (g : B -> D)
    (x : F (A + B)%type) (y : F (A -> B))
    (h : (A -> B) -> (C -> D))
    (Diagram : forall k : A -> B, g ∘ k = h k ∘ f),
    g <$> (x <*[F]? y) = (Either_bimap f g <$[F]> x) <*[F]? (h <$[F]> y).

Lemma free_theorem_1 :
  forall (A B C : Set)
    (f : B -> C) (x : F (A + B)%type) (y : F (A -> B)),
    f <$> (select x y) =
    (fmap[Either A] f <$> x) <*? (fmap[Env A] f <$> y).
Proof.
  intros.
  apply (free_theorem A B A C id f x y (fun k => f ∘ k)).
  now intros.
Qed.

(* Lemma free_theorem_2 : *)
(*   forall (A D C : Type) (F : Type -> Type) *)
(*     (HS : Selective F) *)
(*     (f : A -> C) (x : F (A + D)%type) (y : F (C -> D)), *)
(*     (fmap (mapLeft f) x) <*? y = x <*? ((fun p : C -> D => p ∘ f) <$> y). *)
(* Admitted. *)
(* (* Proof. *) *)
(*   intros. *)
(*   `Begin *)
(*    (fmap (mapLeft f) x <*? y). *)
(*   ≡⟨ reflexivity ⟩ *)
(*    (fmap (Either_bimap f (@id D)) x <*? y). *)
(*   ≡⟨ functor_laws ⟩ *)
(*    (fmap (Either_bimap f (@id D)) x <*? ((fmap[Env C] id) <$[F]> y)). *)
(*   Set Printing Implicit. *)
(*   Check (fun g : C -> D => g ∘ f). *)
(*   Check (free_theorem A D C D F HS f id x (y) *)
(*                       _ _). *)
(*   Check ((fun p : C -> D => p ∘ f) <$> y). *)
(*   ≡⟨ rewrite (free_theorem _ _ _ _ F HS f id)  ⟩ *)
(*    (fmap (@id B) <$[F]> (x <*[F]? y)). *)
(*   ≡⟨ admit ⟩ *)
(*    ((Either_bimap id id <$> x) <*? ((fun g => g ∘ f) <$> y)). *)
(*   ≡⟨ functor_laws ⟩ *)
(*    (x <*? ((fun g => g ∘ f) <$> y)). *)

(* The following lemma is a specialisation of the first free theorem *)
(* in the case when the first argument of select is 'Left' *)
(* Many implicit arguments must be provided explicitly in order for the *)
(* lemma to typecheck properly *)
Corollary free_theorem_1_left :
  forall (X A C : Set)
    (FL : FunctorLaws F)
    (f : X -> C)
    (x : F A)
    (y : F (A -> X)),
    @fmap F _ _ _ f (@select F HS _ _ (@Left A X <$> x) y) =
    @select F HS _ _ ((@Left A C) <$[F]> x)
            ((fmap[Env A] f) <$[F]> y).
Proof.
  intros X A C HFL f x y.
  rewrite free_theorem_1.
  rewrite fmap_comp_x.
  f_equal.
Qed.

Axiom free_theorem_2 :
  forall (A B C : Set) (f : A -> C) (x : F (A + B)%type) (y : F (C -> B)),
    select (fmap (mapLeft f) x) y = select x ((fun g : C -> B => g ∘ f) <$> y).

Axiom free_theorem_3 :
  forall (A B C : Set) (f : C -> A -> B)
                   (x : F (A + B)%type)
                   (y : F C),
    x <*? (f <$> y) = (mapLeft (flip f) <$> x) <*? ((@rev_f_ap _ _) <$> y).

Ltac apply_free_theorems :=
  repeat
    match goal with
    | [ |- context[_ <$> (select _ _)] ] =>
      rewrite free_theorem_1
    end; auto.

End SelectiveParametricity.

Module SelectiveLaws.

Include ApplicativeLaws.

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

Class SelectiveLaws (F : Set -> Set) (HS : Selective F) := {
  has_applicative_laws :> ApplicativeLaws F;

  select_identity : forall (A : Set) (x : F (A + A)%type),
      x <*? (pure id) = either id id <$> x;
  select_distr    : forall (A B : Set) (x : (A + B)%type) (y : F (A -> B)) (z : F (A -> B)),
                    pure x <*? (y *> z) =
                    const id <$> (pure x <*? y) <*> (pure x <*? z);
  select_assoc    : forall (A B C : Set) (x : F ((B + C)%type)) (y : F (Either A (B -> C)))
                                          (z : F (A -> B -> C)),
                     x <*? (y <*? z) = (law3_f <$> x) <*? (law3_g <$> y) <*? (law3_h <$> z)
}.

End SelectiveLaws.
