Require Import Hask.Prelude.
Require Import Data.Functor.
Require Import Control.Applicative.
Require Import FunctionalExtensionality.

Inductive Either (A B : Set) : Set :=
    Left  : A -> Either A B
  | Right : B -> Either A B.

Arguments Left {_} {_}.
Arguments Right {_} {_}.

Global Close Scope nat_scope.
Notation "x + y" := (Either x y) : type_scope.

Definition either {A B C : Set} (f : A -> C) (g : B -> C) (x : A + B) : C :=
  match x with
  | Left a => f a
  | Right b => g b
  end.

Definition mapLeft {A B C : Set} (f : A -> C) (x : A + B) : C + B :=
  match x with
  | Left l => Left (f l)
  | Right r => Right r
  end.

Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

Add Parametric Morphism {A B C} : (fun f => @mapLeft A C B f)
  with signature (pointwise_relation _ eq ==> eq ==> eq)
    as mapLeft_isomorphism.
Proof.
  intros. f_equal. extensionality a. intuition.
Qed.

Definition mapRight {E X Y : Set} (f : X -> Y) (x : Either E X) : Either E Y :=
  match x with
  | Left e   => Left e
  | Right x' => Right (f x')
  end.

Add Parametric Morphism {A B C : Set} : (fun f => @mapRight A C B f)
  with signature (pointwise_relation _ eq ==> eq ==> eq)
    as mapRight_isomorphism.
Proof.
  intros. f_equal. extensionality a. intuition.
Qed.

Definition Either_bimap {A B X Y : Set} (f : A -> B) (g : X -> Y) (x : Either A X) : Either B Y :=
  match x with
  | Left a  => Left (f a)
  | Right x => Right (g x)
  end.

Lemma Either_bimap_id :
  forall (A B : Set),
    Either_bimap (@id A) (@id B) = id.
Proof.
  intros A B.
  extensionality x.
  destruct x; trivial.
Qed.

Definition Either_ap {E X Y : Set} (f : Either E (X -> Y)) (x : Either E X)
  : Either E Y :=
  match f with
  | Left e   => Left e
  | Right f' => match x with
    | Left e   => Left e
    | Right x' => Right (f' x')
    end
  end.

Definition Either_join {E X : Set} (x : Either E (Either E X)) : Either E X :=
  match x with
  | Left e           => Left e
  | Right (Left e)   => Left e
  | Right (Right x') => Right x'
  end.

Instance Either_Functor {E : Set} : Functor (Either E) :=
{ fmap := @mapRight E
}.

Import FunctorLaws.

Program Instance Either_FunctorLaws {E : Set} : FunctorLaws (Either E).
Obligation 1.
extensionality x. now destruct x.
Defined.
Obligation 2.
extensionality x. now destruct x.
Defined.

Lemma Either_fmap_left_cancel :
  forall (A B C : Set) (f : B -> C),
  fmap[Either A] f ∘ Left = Left.
Proof. intros. extensionality x. now simpl. Qed.

Lemma Either_bimap_fmap_fuse :
  forall (A B C D X : Set)
         (f : B -> C) (g : B -> D) (h : X -> B),
  Either_bimap f g ∘ mapRight h = Either_bimap f (g ∘ h).
Proof.
  intros A B C D X f g h.
  extensionality x.
  now destruct x.
Qed.

Lemma Either_bimap_fmap_fuse_x :
  forall (A B C D X : Set)
         (f : B -> C) (g : B -> D) (h : X -> B) x,
  Either_bimap f g (mapRight h x) = Either_bimap f (g ∘ h) x.
Proof.
  intros A B C D X f g h x.
  now destruct x.
Qed.

Lemma Either_bimap_mapLeft_fuse :
  forall (A B C D X : Set)
         (f : B -> C) (g : B -> D) (h : C -> X),
  mapLeft h ∘ Either_bimap f g = Either_bimap (h ∘ f) g.
Proof.
  intros A B C D X f g h.
  extensionality x.
  now destruct x.
Qed.

Lemma Either_bimap_mapLeft_fuse_x :
  forall (A B C D X : Set)
         (f : B -> C) (g : B -> D) (h : C -> X) x,
  mapLeft h (Either_bimap f g x) = Either_bimap (h ∘ f) g x.
Proof.
  intros A B C D X f g h x.
  now destruct x.
Qed.

Lemma Either_map_to_fmap :
  forall (A B C : Set)
         (f : B -> C),
    @mapRight A B C f = fmap f.
Proof. now simpl fmap. Qed.

Instance Either_Applicative {E} : Applicative (Either E) :=
{ is_functor := Either_Functor
; pure := @Right E
; ap := @Either_ap E
}.

Import ApplicativeLaws.

Program Instance Either_ApplicativeLaws {E} : ApplicativeLaws (Either E).
Obligation 1.
extensionality x. now destruct x.
Defined.
Obligation 2.
destruct w; destruct v; destruct u; trivial.
Defined.
