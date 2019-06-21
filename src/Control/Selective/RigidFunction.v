Require Import Coq.Program.Basics.
Require Import Hask.Prelude.
Require Import Data.Functor.
Require Import Data.Either.
Require Import Control.Applicative.
Require Import Control.Selective.
Require Import FunctionalExtensionality.
Require Import Omega.

Generalizable All Variables.

Inductive Select (F : Type -> Type) (A : Type) :=
    Pure   : A -> Select F A
  | MkSelect : forall B, Select F (B + A) -> F (B -> A) -> Select F A.

Arguments Pure {F} {A}.
Arguments MkSelect {F} {A} {B}.


Fixpoint Select_map {A B : Type} {F : Type -> Type} `{Functor F}
         (f : A -> B) (x : Select F A) : Select F B :=
  match x with
  | Pure a => Pure (f a)
  | MkSelect x y => MkSelect (Select_map (fmap f) x)
                            (fmap (fun k : _ -> A => f \o k) y)
  end.

Fixpoint Select_depth {A : Type} {F : Type -> Type}
         (x : Select F A) : nat :=
  match x with
  | Pure a => O
  | MkSelect y _ => S (Select_depth y)
  end.

Lemma Select_fmap_preserves_depth {A B : Type} `{Functor F} :
  forall (x : Select F A) (f : A -> B),
  Select_depth (Select_map f x) = Select_depth x.
Proof.
  intros x.
  revert B.
  induction x as [| A b s IH handler]; trivial; simpl in *; intros f1 B.
  - simpl Select_map. simpl Select_depth. now rewrite IH.
Qed.

Definition law3_f {A B C : Type}
           (x : B + C) : B + (A + C) := Right <$> x.

Definition law3_g {A B C : Type}
           (y : A + (B -> C)) : B -> A * B + C :=
  fun a => Either_bimap (fun p => pair p a) (fun f => f a) y.

Definition law3_h  {A B C : Type}
           (f : A -> B -> C) : A * B -> C := uncurry f.

Definition Select_depth_order {A : Type} {F : Type -> Type}
           (x : Select F A) (y : Select F A) :=
  Select_depth x < Select_depth y.

Hint Constructors Acc.

(* Theorem Select_depth_order_wf : forall (A B : Type) (F : Type -> Type), well_founded (@Select_depth_order A F). *)
(* Admitted. *)

Require Import FunInd.
Require Import  Recdef.

(* Function Select_select {A B : Type} `{H : Functor F} *)
(*          (x : Select F (A + B)) (handler : (Type * Select F (A -> B))) *)
(*   {wf (fun a => @Select_depth_order (fst a) F) handler} : (Select F B) := *)
(*   match handler with *)
(*   | pair P (Pure y) => Select_map (either y id) x *)
(*   | pair Q (MkSelect y z) => *)
(*     MkSelect (Select_select (Select_map law3_f x) (pair (A -> Q * A + B) (Select_map law3_g y))) (law3_h <$> z) *)
(*   end. *)

Definition Select_erase_type {A : Type} `{Functor F} (x : Select F A) :
  Select F unit :=
  Select_map (const tt) x.

Function Select_select_help {A B : Type} `{H : Functor F}
         (x : Select F (A + B)) (handler : Select F (A -> B))
         (dummy : Select F unit) (Heqdummy : dummy = Select_erase_type handler)
  {measure (fun a => Select_depth (Select_erase_type a)) dummy} : (Select F B) :=
  match handler with
  | Pure y => Select_map (either y id) x
  | MkSelect y z =>
    let handler' := Select_map law3_g y
    in  MkSelect (Select_select_help (Select_map law3_f x) handler'
                                     (Select_erase_type handler') eq_refl) (law3_h <$> z)
  end.
Proof.
  intros A B F H x handler dummy G y z HMkSelect Heqdummy.
  rewrite Heqdummy.
  unfold Select_erase_type.
  repeat rewrite Select_fmap_preserves_depth.
  simpl Select_depth. omega.
Qed.

Definition Select_select  {A B : Type} `{H : Functor F}
           (x : Select F (A + B)) (handler : Select F (A -> B)) :
  Select F B :=
  Select_select_help A B F H x handler (Select_erase_type handler) eq_refl.

Lemma Select_select_equation_1 : forall (A B : Type) `(H : Functor F)
         (x : Select F (A + B)) (y : A -> B),
    Select_select x (Pure y) = Select_map (either y id) x.
Proof.
  intros A B F H x y.
  unfold Select_select.
  now rewrite Select_select_help_equation.
Qed.

Lemma Select_select_equation_2 : forall (A B C : Type) `(H : Functor F)
         (x : Select F (A + B)) (y : Select F (C + (A -> B))) (z : F (C -> A -> B)),
    Select_select x (MkSelect y z) =
     MkSelect (Select_select (Select_map law3_f x) (Select_map law3_g y)) (law3_h <$> z).
Proof.
  intros A B C F H x y z.
  unfold Select_select.
  now rewrite Select_select_help_equation.
Qed.

Require Import Coq.Program.Equality.

Theorem select_selective_law3_assoc
  {A B C : Type} {F : Type -> Type} `{Functor F}
  (x : Select F (B + C))
  (y : Select F (A + (B -> C)))
  (z : Select F (A -> B -> C)) :
  Select_select x (Select_select y z) =
  Select_select (Select_select (Select_map law3_f x) (Select_map law3_g y)) (Select_map law3_h z).
Proof.
  dependent induction z.
  - simpl Select_map.
    repeat rewrite Select_select_equation_1.
    admit.
  - repeat rewrite Select_select_equation_2.
    simpl Select_map.
    repeat rewrite Select_select_equation_2.
    f_equal.



