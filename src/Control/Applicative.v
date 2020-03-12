Require Export Hask.Prelude.
Require Export Hask.Data.Functor.
Require Export Hask.Data.Functor.Const.
Require Import FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

Reserved Notation "f <*> g" (at level 28, left associativity).

Class Applicative (F : Set -> Set) := {
  is_functor :> Functor F;

  pure : forall a : Set, a -> F a;
  ap   : forall a b : Set, F (a -> b) -> F a -> F b
    where "f <*> g" := (ap f g)
}.

Arguments pure {F _ _} _.
Arguments ap   {F _ _ _} _ x.

(* Add Parametric Morphism {A} `{Applicative F} : (@pure F _ A) *)
(*   with signature (pointwise_relation _ eq ==> eq ==> eq) *)
(*     as pure_isomorphism. *)
(* Proof. *)
(*   intros. *)
(*   f_equal. *)
(*   extensionality e. *)
(*   apply H0. *)
(* Qed. *)

Section WithApplicative.
  Context {F : Set -> Set}.
  Context {HA : Applicative F}.

  Lemma pure_ext : forall (A : Set) (x y : A),
      x = y -> pure x = pure y.
  Proof. intros. now subst. Qed.

  Definition liftA2 {A B C : Set}
             (f : A -> B -> C) (x : F A) (y : F B) : F C := ap (fmap f x) y.

  (* Lemma sequence_ap : *)
  (*   forall (A B : Set) (p : F A) (q : F B), *)
  (*     p *> q = (const id) <$> p <*> q. *)
  (* Proof. reflexivity. Qed. *)
End WithApplicative.

Notation "pure[ M ]" := (@pure M _ _) (at level 19, M at next level).
Notation "pure[ M N ]" := (@pure (fun X => M (N X)) _ _) (at level 9).

Notation "ap[ M ]" := (@ap M _ _ _) (at level 9).
Notation "ap[ M N ]" := (@ap (fun X => M (N X)) _ _ _) (at level 9).
Notation "ap[ M N O ]" := (@ap (fun X => M (N (O X))) _ _ _) (at level 9).

Infix "*>" := (liftA2 (const id)) (at level 28, left associativity).
Infix "<*" := (liftA2 const) (at level 28, left associativity).

Infix "<*>" := ap (at level 28, left associativity).

Module ApplicativeLaws.

Import FunctorLaws.

Class ApplicativeLaws (F : Set -> Set) {FIsApplicative : Applicative F} := {
  has_functor_laws :> FunctorLaws F;

  ap_id : forall A : Set, ap (pure (@id A)) = id;
  ap_comp : forall (A B C : Set) (v : F (A -> B)) (u : F (B -> C)) (w : F A),
    pure (fun f g x => f (g x)) <*> u <*> v <*> w = u <*> (v <*> w);
  ap_homo : forall (A B : Set) (x : A) (f : A -> B),
    pure f <*> pure x = pure (f x);
  ap_interchange : forall (A B : Set) (y : A) (u : F (A -> B)),
    u <*> pure y = pure (fun f => f y) <*> u;

  ap_fmap : forall (A B : Set) (f : A -> B),
    ap (pure f) = @fmap _ is_functor _ _ f
}.
Section WithApplicativeLaws.
  Context (F : Set -> Set).
  Context (HA : Applicative F).
  Context (HAL : ApplicativeLaws F).

  Corollary fmap_pure (A B : Set) :
    forall (f : A -> B), fmap f ∘ pure = pure ∘ f.
  Proof.
    intros f.
    extensionality x.
    cbn.
    rewrite <- ap_fmap.
    apply ap_homo.
  Qed.

  Corollary fmap_pure_x (A B : Set) :
    forall (f : A -> B) (x : A), fmap f (pure x) = pure (f x).
  Proof.
    intros.
    replace (pure (f x)) with ((pure ∘ f) x).
    now rewrite <- fmap_pure.
    reflexivity.
  Qed.
End WithApplicativeLaws.

Ltac apply_applicative_laws :=
  repeat
    match goal with
    | [ |- context[fmap[?F] id] ] =>
      rewrite fmap_id
    | [ |- context[fmap[?F] _ (fmap[?F] _ _)] ] =>
      rewrite fmap_comp_x

    | [ |- context[fmap[?F] _ (pure[?F] _)] ] =>
      rewrite fmap_pure_x
    | [ |- context[ap[?F] (pure[?F] id) _] ] =>
      rewrite ap_id
    | [ |- context[ap[?F] (pure[?F] _) _] ] =>
      rewrite ap_fmap
    | [ |- context[ap[?F] (pure[?F] _)] ] =>
      rewrite ap_fmap
    | [ |- context[ap[?F] (pure[?F] _) (pure[?F] _)] ] =>
      rewrite ap_homo
    | [ |- context[_ <*> pure[?F] _] ] =>
      rewrite ap_interchange

    | [ |- context[fmap[?F] id] ] =>
      setoid_rewrite fmap_id
    | [ |- context[fmap[?F] _ (fmap[?F] _ _)] ] =>
      setoid_rewrite fmap_comp_x

    | [ |- context[fmap[?F] _ (pure[?F] _)] ] =>
      setoid_rewrite fmap_pure_x
    | [ |- context[ap[?F] (pure[?F] id) _] ] =>
      setoid_rewrite ap_id
    | [ |- context[ap[?F] (pure[?F] _) _] ] =>
      setoid_rewrite ap_fmap
    | [ |- context[ap[?F] (pure[?F] _)] ] =>
      setoid_rewrite ap_fmap
    | [ |- context[ap[?F] (pure[?F] _) (pure[?F] _)] ] =>
      setoid_rewrite ap_homo
    | [ |- context[_ <*> pure[?F] _] ] =>
      setoid_rewrite ap_interchange
    end; auto.

End ApplicativeLaws.
