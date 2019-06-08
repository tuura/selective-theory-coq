Require Import Coq.Program.Basics.
Require Import Hask.Prelude.
Require Import Data.Either.
Require Import Data.Monoid.
Require Import Data.Functor.
Require Import Control.Applicative.
Require Import Control.Selective.
(* Require Import Data.Over. *)
Require Import Coq.Strings.String.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Classes.Morphisms_Prop.
Require Import FunctionalExtensionality.
Require Import Omega.
From Equations Require Import Equations.

Generalizable All Variables.
(* Functors preserve extensional equality for the applied function.
   This is needed to perform setoid rewriting within the function
   passed to a functor. *)
Add Parametric Morphism {A B} `{Functor F} : (@fmap F _ A B)
  with signature (pointwise_relation _ eq ==> eq ==> eq)
    as mul_isomorphism.
Proof.
  intros.
  f_equal.
  extensionality e.
  apply H0.
Qed.

(* Inductive Select (f : Type -> Type) (a : Type) := *)
(*     Pure   : a -> Select f a *)
(*   | MkSelect : forall b, Select f (b + a) -> f (b -> a) -> Select f a. *)
Inductive Select (F : Type -> Type) (A : Type) :=
    Pure   : A -> Select F A
  | MkSelect : forall X, Select F ((X -> A) + A) -> F X -> Select F A.

Arguments Pure {F} {A}.
Arguments MkSelect {F} {A} {X}.

    (* fmap f (Pure a)     = Pure (f a) *)
    (* fmap f (Select x y) = Select (bimap (f.) f <$> x) y *)


(******************************************************************************)
(************************ Functor and FunctorLaws *****************************)
(******************************************************************************)
Equations Select_map {A B : Type} {F : Type -> Type}
           (f : A -> B) (x : Select F A) : Select F B :=
Select_map f (Pure a) => Pure (f a);
Select_map f (MkSelect x y) =>
  MkSelect (Select_map (Either_bimap (fun k : _ -> A => f \o k) f) x) y.

Program Instance Select_Functor (F : Type -> Type)
  `{Functor F} : Functor (Select F) := {
  fmap := fun _ _ f x => Select_map f x
}.

(* Auxiliary lemmas for proving Functor laws *)
Definition id_f {A : Type} (x : A) := x.

Lemma id_x_is_x {A : Type}:
  forall (x : A), id x = x.
Proof. intros x. reflexivity. Qed.

Lemma id_comp {A B : Type}:
  forall (f : A -> B), (id \o f) = f.
Proof.
  intros f.
  extensionality x.
  now unfold comp.
Qed.

Import FunctorLaws.

Lemma fmap_rewrite_compose {A B C : Type} `{Functor F} :
  forall (f : B -> C) (g : A -> B) (x : F A),
    fmap f (fmap g x) = (fmap f \o fmap g) x.
Proof.
  intros f g x.
  reflexivity.
Qed.

Lemma bimap_id :
  forall (A B : Type),
    Either_bimap (@id A) (@id B) = id.
Proof.
  intros A B.
  extensionality x.
  destruct x; trivial.
Qed.

Program Instance Select_FunctorLaws `{FunctorLaws F} : FunctorLaws (Select F).
(* Theorem Select_Functor_law1 {A : Type} *)
(*         `{Functor F} `{FunctorLaws F} : *)
(*   forall (x : Select F A), fmap id x = id x. *)
Obligation 1.
unfold id.
extensionality x.
generalize dependent x.
generalize dependent a.
induction x; simpl in *; trivial.
rewrite Select_map_equation_2.
f_equal.
assert (forall A, (fun x0 : A => x0) = id).
{ reflexivity. }
repeat rewrite H1 in *.
rewrite bimap_id.
now rewrite IHx.
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
  remember (Either_bimap (fun k : X -> b => f0 \o k) f0) as p.
  remember (Either_bimap (fun k : X -> A => g \o k) g) as q.
  remember (Either_bimap (fun k : X -> A => (f0 \o g) \o k) (f0 \o g)) as r.
  assert (p \o q = r).
  { extensionality y.
    simpl. rewrite Heqp. rewrite Heqq. rewrite Heqr.
    destruct y; trivial.
  }
  rewrite <- H1.
  now rewrite IHx.
Qed.

(* This is a halper function used in the Select_selectBy definition *)
Definition g {A B C D E : Type}
           (f : A -> ((B -> C) + C))
           (a : A) :
  Either (((D -> B) + B) -> ((D -> C) + C))
         (E + C) :=
  match f a with
  | inr r => Right (Right r)
  | inl l => Left  (Either_bimap (fun k => l \o k) l)
  end.

Equations Select_selectBy {A B C : Type} `{Functor F}
          (f : A -> ((B -> C) + C))
          (x : Select F A)
          (a : Select F B) : Select F C :=
Select_selectBy f x (Pure y)       := (either (fun k => k y) id \o f) <$> x;
Select_selectBy f x (MkSelect y z) := MkSelect (Select_selectBy (g f) x y) z.

Definition Select_ap {A B : Type} `{Functor F}
           (f : Select F (A -> B)) (x : Select F A) : Select F B :=
  Select_selectBy Left f x.

Program Instance Select_Applicative
        (F : Type -> Type) `{Functor F} : Applicative (Select F) :=
  { is_functor := Select_Functor F
  ; pure _ x := Pure x
  ; ap _ _ f x := Select_ap f x
}.

Import ApplicativeLaws.

(* (forall (F : Type -> Type) (H : Functor F), *)
(*  FunctorLaws F -> forall a : Type, ap[ Select F] ((pure[ Select F]) id) = id). *)
(* pure id <*> v = v   *)

Polymorphic Definition pid {A : Type} (a : A) := a.

Lemma either_left :
  forall (A B C : Type) (f : A -> C) (g : B -> C),
  (either f g) \o inl = f.
Proof.
  intros A B C f g.
  extensionality x.
  trivial.
Qed.

Lemma id_is_unique :
  forall (A : Type) (f : A -> A), f = id.
Admitted.

Program Instance Select_ApplicativeLaws `{FunctorLaws F} : ApplicativeLaws (Select F).
Obligation 1.
  extensionality x.
  unfold Select_ap.
  induction x; trivial.
  - rewrite Select_selectBy_equation_2.
    rewrite id_x_is_x.
    f_equal.
    (* Looks like we're stuck; the gool here looks like this: *)
    (* IHx : Select_selectBy inl (Pure id) x = id x *)
    (* ============================ *)
    (* Select_selectBy (g inl) (Pure id) x = x *)
    (* We need to prove the following assertion: *)
    assert (g inl = inl).
    (* But it doesn't typecheck *)
Admitted.
Obligation 2.
Admitted.
(* Interchange *)
(* u <*> pure y = pure ($ y) <*> u *)
Obligation 5.
extensionality x.
unfold Select_ap.
induction x; trivial.
- rewrite Select_selectBy_equation_2.
  rewrite Select_map_equation_2.
  f_equal.
Obligation 4.
Admitted.
(* Proof. *)
(*   revert u y. *)
(*   intros f y. *)
(*   destruct f. *)
(*   - trivial. *)
(*   - unfold Select_ap. *)
(*     rewrite Select_selectBy_equation_1. *)
(*     rewrite Select_selectBy_equation_2. *)
(*     rewrite either_left. *)
(*     simpl. *)
(*     rewrite Select_map_equation_2. *)
(*     f_equal. *)
Admitted.
Obligation 5.



Theorem Select_Applicative_law1
        `{FunctorLaws F} :
  forall (A : Type) (x : Select F A),
  Select_ap (Pure id) x = id x.
Proof.
  unfold Select_ap.
  induction x as [| A B y IH z]; trivial;
  rewrite Select_selectBy_equation_2.
  rewrite id_x_is_x.
  rewrite id_x_is_x in IH.
  f_equal.
Admitted.

