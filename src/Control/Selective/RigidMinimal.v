Require Import Hask.Control.Iso.
Require Import Hask.Prelude.
Require Import Data.Functor.
Require Import Data.Either.
Require Import Control.Applicative.
Require Import Control.Selective.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Equations.Equations.

Set Universe Polymorphism.
Generalizable All Variables.

Inductive Select (F : Type -> Type) (A : Type) :=
    Pure   : A -> Select F A
  | MkSelect : forall B, Select F (B + A) -> F (B -> A) -> Select F A.

Arguments Pure {F} {A}.
Arguments MkSelect {F} {A} {B}.

Equations Select_map {A B : Type} {F : Type -> Type} `{Functor F}
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

Program Instance Select_Functor `{Functor F} : Functor (Select F) := {
  fmap := fun _ _ f x => Select_map f x
}.

Import FunctorLaws.

Program Instance Select_FunctorLaws `{FunctorLaws F} : FunctorLaws (Select F).
(* Theorem Select_Functor_law1 {A : Type} *)
(*         `{Functor F} `{FunctorLaws F} : *)
(*   forall (x : Select F A), fmap id x = id x. *)
Obligation 1.
unfold id.
extensionality x.
generalize dependent x.
generalize dependent a.
induction x; trivial.
rewrite Select_map_equation_2.
assert (forall A, (fun x0 : A => x0) = id) as H_subst_id.
{ reflexivity. }
f_equal; repeat rewrite H_subst_id in *; rewrite fmap_id.
- now rewrite IHx.
- now unfold id.
Qed.
(* Theorem Select_Functor_law2 {A B C : Type} *)
(*         `{Functor F} `{FunctorLaws F} : *)
(*   forall (f : B -> C) (g : A -> B) (x : Select F A), *)
(*   ((Select_map f) \o (Select_map g)) x = Select_map (f \o g) x. *)
Obligation 2.
extensionality x.
simpl.
revert b c f g.
induction x.
- trivial.
- intros b c f0 g.
  repeat rewrite Select_map_equation_2.
  f_equal.
  + rewrite <- fmap_comp. now rewrite IHx.
  + admit.
Admitted.

Definition law3_f {A B C : Type}
           (x : B + C) : B + (A + C) := Right <$> x.

Definition law3_g {A B C : Type}
           (y : A + (B -> C)) : B -> A * B + C :=
  fun a => Either_bimap (fun p => pair p a) (fun f => f a) y.

Definition law3_h  {A B C : Type}
           (f : A -> B -> C) : A * B -> C := uncurry f.

Equations Select_select {A B : Type} `{Functor F}
          (x : Select F (A + B)) (handler : Select F (A -> B))
  : (Select F B) by wf (Select_depth handler) lt :=
Select_select x (Pure y) := Select_map (either y id) x;
Select_select x (MkSelect y z) :=
  MkSelect (Select_select (Select_map law3_f x) (Select_map law3_g y)) (fmap law3_h z).
Obligation 1.
rewrite Select_fmap_preserves_depth.
rewrite Select_depth_equation_2.
omega.
Qed.
