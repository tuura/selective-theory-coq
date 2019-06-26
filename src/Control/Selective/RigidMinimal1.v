Require Import Coq.Program.Basics.
Require Import Hask.Prelude.
Require Import Data.Functor.
Require Import Data.Either.
Require Import Control.Applicative.
Require Import Control.Selective.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Equations.Equations.

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

Definition law3_f {A B C : Type}
           (x : B + C) : B + (A + C) := Right <$> x.

Definition law3_g {A B C : Type}
           (y : A + (B -> C)) : B -> A * B + C :=
  fun a => Either_bimap (fun p => pair p a) (fun f => f a) y.

Definition law3_h  {A B C : Type}
           (f : A -> B -> C) : A * B -> C := uncurry f.

From Coq Require Import Extraction Relation_Definitions.
Require Import Equations.Prop.Classes.
Require Import Equations.Prop.Telescopes.

Section Tele.

Set Printing Universes.

Universe a. (* Top.1559 *)
Universe b. (* Top.1560 *)
Universe c. (* Top.1562 *)
Universe i. (* Top.1564 *)
Universe j. (* Hask.Data.Functor.1 *)

Definition Select_tele :=
           (ext@{i} Type@{a}
              (fun A : Type@{a} =>
               ext@{i} Type@{b}
                 (fun B : Type@{b} =>
                  ext@{i} (Type@{j} -> Type@{c})
                    (fun F : Type@{j} -> Type@{c} =>
                     ext@{i} (Functor F)
                       (fun _ : Functor F =>
                        ext@{i} (Select F (A + B)) (fun _ : Select F (A + B) => tip@{i} (Select F (A -> B)))))))).

Definition Select_tele_fn :=
  (fun (A : Type@{a}) (B : Type@{b}) (F : Type@{j} -> Type@{c})
     (_ : Functor F) (_ : Select F (A + B)) (handler : Select F (A -> B))
            => Select_depth handler).

Definition Select_tele_measure := tele_measure Select_tele nat Select_tele_fn lt.

Check (@WellFounded (tele_sigma Select_tele) Select_tele_measure).

Equations Select_select {A B : Type} `{Functor F}
          (x : Select F (A + B)) (handler : Select F (A -> B))
  : (Select F B) by wf (Select_depth handler) lt :=
Select_select x (Pure y) := either y id <$> x;
Select_select x (MkSelect y z) :=
  MkSelect (Select_select (Select_map law3_f x) (Select_map law3_g y)) (fmap law3_h z).

End Tele.
