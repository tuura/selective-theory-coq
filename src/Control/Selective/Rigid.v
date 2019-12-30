Require Import Hask.Control.Iso.
Require Import Hask.Prelude.
Require Import Data.Functor.
Require Import Data.Either.
Require Import Control.Applicative.
Require Import Control.Selective.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Equations.Equations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

Set Universe Polymorphism.
Generalizable All Variables.

Inductive Select (F : Type -> Type) (A : Type) :=
    Pure   : A -> Select F A
  | MkSelect : forall B, Select F (B + A) -> F (B -> A) -> Select F A.

Arguments Pure {F} {A}.
Arguments MkSelect {F} {A} {B}.

Equations Select_map {A B : Type} `{Functor F}
           (f : A -> B) (x : Select F A) : Select F B :=
Select_map f (Pure a)       => Pure (f a);
Select_map f (MkSelect x y) => MkSelect (Select_map (fmap f) x)
                                        (fmap (fun k : _ -> A => f \o k) y).

Equations Select_depth {A : Type} {F : Type -> Type}
         (x : Select F A) : nat :=
Select_depth (Pure a)       := O;
Select_depth (MkSelect y _) := S (Select_depth y).

Lemma Select_fmap_preserves_depth {A B : Type} `{Functor F} :
  forall (x : Select F A) (f : A -> B),
  Select_depth (Select_map f x) = Select_depth x.
Proof.
  intros x.
  revert B.
  induction x as [| A b s IH handler]; trivial; simpl in *; intros f1 B.
  - repeat rewrite Select_map_equation_2. simp Select_depth. now rewrite IH.
Qed.

(***************************************************************)
Instance Select_Functor {F : Type -> Type} {_ : Functor F} : Functor (Select F) := {
  fmap := fun _ _ f x => Select_map f x
}.

Definition law3_f {A B C : Type}
           (x : B + C) : B + (A + C) := Right <$> x.

Lemma law3_f_cancel :
  forall (A B C : Type),
  (@law3_f A _ _) ∘ (@Left B C) = Left.
Proof. intros. extensionality x. now simpl. Qed.

Definition law3_g {A B C : Type}
           (y : A + (B -> C)) : B -> A * B + C :=
  fun a => Either_bimap (fun p => pair p a) (fun f => f a) y.

Definition law3_h  {A B C : Type}
           (f : A -> B -> C) : A * B -> C := uncurry f.

Equations Select_select {A B : Type} {F : Type -> Type} {HF : Functor F}
          (x : Select F (A + B)) (handler : Select F (A -> B))
  : (Select F B) by wf (Select_depth handler) lt :=
Select_select x (Pure y) := fmap[Select F] (either y id) x;
Select_select x (MkSelect y z) :=
  MkSelect (Select_select (fmap[Select F] law3_f x) (fmap[Select F] law3_g y))
           (fmap[F] law3_h z).
Obligation 1.
simpl.
rewrite Select_fmap_preserves_depth.
rewrite Select_depth_equation_2.
omega.
Defined.

Definition Select_ap {A B : Type} `{Functor F}
           (f : Select F (A -> B)) (x : Select F A) : Select F B :=
  Select_select (Left <$> f) (rev_f_ap <$> x).

(***************************************************************)
Global Instance Select_Applicative `{Functor F} : Applicative (Select F) := {
  pure _ x := Pure x;
  ap _ _ f x  := Select_ap f x
}.

(***************************************************************)
Global Instance Select_Selective `{Functor F} : Selective (Select F) := {
  select _ _ x f := Select_select x f
}.

(***************************************************************)
(***************************************************************)
(***************************************************************)

(* (* ?O(n)? select implementation *) *)
Fixpoint Select_select_go {A B C : Type} `{Functor F}
         (x : Select F (A + B)) (s : Select F C) (k : C -> (A -> B)) {struct s} :
         Select F B :=
  match s with
  | Pure y => either (k y) id <$> x
  | MkSelect y z =>
    MkSelect (Select_select_go (law3_f <$> x)
                               y
                               (comp law3_g (mapRight k))
             )
             (comp law3_h (comp k) <$> z)
  end.

Fixpoint Select_select'  {A B : Type} `{Functor F}
         (x : Select F (B + A)) (f : Select F (B -> A)) : Select F A :=
  Select_select_go x f id.
