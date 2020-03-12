Require Import FunctionalExtensionality.
Require Import Reasoning.
Require Import Hask.Prelude.
Require Import Data.Either.
Require Import Data.Monoid.
Require Import Hask.Data.Functor.
Require Import Hask.Data.Functor.Const.
Require Import Hask.Control.Applicative.
Require Import Hask.Control.Selective.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

Import FunctorLaws.
Import ApplicativeLaws.
Import SelectiveLaws.

Reserved Notation "m >>= f" (at level 42, right associativity).
Reserved Notation "m >>[ F ]= f" (at level 42, right associativity).

Class Monad (F : Set -> Set) := {
  (* is_applicative :> Applicative F; *)
  ret : forall A : Set, A -> F A;
  bind : forall (A B : Set), (A -> F B) -> F A -> F B
}.

Arguments ret {_ _ _} _.
Arguments bind {_ _ _ _} _ _.

Declare Scope monad_scope.
Notation "m >>= f" := (bind f m) (at level 42, right associativity) : monad_scope.
Notation "m >>[ F ]= f" := (bind (F:=F) f m)
  (at level 42, right associativity) : monad_scope.
Open Scope monad_scope.

Global Instance Monad_Functor (F : Set -> Set) (HM : Monad F) :
  Functor F := {
    fmap _ _ f x := x >>= (ret ∘ f)
  }.

Definition apM {A B : Set} {F : Set -> Set} {HM : Monad F}
           (f : F (A -> B)) (x : F A) : F B :=
  f >>= fun k => k <$> x.

Global Instance Monad_Applicative (F : Set -> Set) (HM : Monad F) :
  Applicative F := {
    pure x := @ret F _ x;
    ap _ _ f x := apM f x
  }.

Class MonadLaws (F : Set -> Set) (HM : Monad F) := {
  (* has_applicative_laws :> ApplicativeLaws F; *)
  left_id : forall (A B : Set) (x : A) (f : A -> F B),
            ret x >>= f = f x;
  right_id : forall (A : Set) (m : F A), m >>= ret = m;
  assoc: forall (A B C : Set) (m : F A) (f : A -> F B) (g : B -> F C),
      (m >>= f) >>= g = m >>= (fun x => f x >>= g)
}.

Global Program Instance Monal_FunctorLaws (F : Set -> Set)
       (HM : Monad F) (HML : MonadLaws F HM) : FunctorLaws F.
Obligation 1.
  extensionality x.
  unfold comp.
  now rewrite right_id.
Defined.
Obligation 2.
  extensionality x.
  unfold comp.
  rewrite assoc.
  f_equal.
  extensionality z.
  now rewrite left_id.
Defined.

Definition selectM {A B : Set} {F : Set -> Set} {HM : Monad F}
           (x : F (A + B)) (y : F (A -> B)) : F B :=
  x >>[F]= fun i => match i with
              | Left a => rev_f_ap a <$> y
              | Right b => pure b
              end.

Global Instance Monad_Selective (F : Set -> Set) (HM : Monad F) :
  Selective F := {
    select _ _ x f := selectM x f
  }.

Program Instance MonadLaws_SelectiveLaws (F : Set -> Set)
  (HM : Monad F)
  (HML : MonadLaws F HM) :
  (@SelectiveLaws F (Monad_Selective F HM)).
Admit Obligations.

Lemma fmap_left_bind : forall (A B C : Set) (F : Set -> Set) (HM : Monad F) (HML : MonadLaws F HM)
            (f : F A) (g : (A + C) -> F B),
      fmap[F] Left f >>[F]= g = f >>= (g ∘ Left).
Proof.
  intros. unfold comp.
  simpl.
  rewrite assoc.
  f_equal.
  extensionality x.
  simpl.
  now setoid_rewrite left_id.
Qed.

Lemma Monad_ap_is_apS
      (A B : Set) (F : Set -> Set)
      (HM : Monad F) (HML : MonadLaws F HM) :
      forall (f : F (A -> B)) (x : F A), f <*> x = apS f x.
Proof.
  intros.
  `Begin
   (f <*> x).
  ≡⟨ reflexivity ⟩
   (apM f x).
  ≡⟨ now unfold apM ⟩
   (f >>= (fun k : A -> B => fmap k x)).
  ≡⟨ f_equal ⟩
   (f >>= ((fun i : (A -> B) + B =>
      match i with
      | Left k => fmap k x
      | Right b => pure b
      end) ∘ Left)).
  ≡⟨ now rewrite fmap_left_bind ⟩
   (fmap Left f >>= fun i : (A -> B) + B =>
      match i with
      | Left k => fmap k x
      | Right b => pure b
      end).
  ≡⟨ f_equal; extensionality i; destruct i; functor_laws ⟩
   (fmap Left f >>= fun i : (A -> B) + B =>
      match i with
      | Left k => fmap (rev_f_ap k) (fmap rev_f_ap x)
      | Right b => pure b
      end).
  ≡⟨ now unfold selectM ⟩
   (selectM (fmap Left f) (fmap rev_f_ap x)).
  unfold selectM.
  ≡⟨ reflexivity ⟩
   (fmap Left f <*? fmap rev_f_ap x).
  ≡⟨ now unfold apS ⟩
   (apS f x)
  `End.
Qed.
