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

Print nat_ind.
Print nat_rect.

(* Polymorphic Cumulative *)
Inductive FreeA (f : Type -> Type) (a : Type) :=
    Pure : a -> FreeA f a
  | MkAp : forall b, f (b -> a) -> FreeA f b -> FreeA f a.

Arguments Pure {f} {a}.
Arguments MkAp {f} {a} {b}.

Check FreeA_ind.

Fixpoint FreeA_map {A B : Type} `{Functor F}
           (g : (A -> B)) (a : FreeA F A) : FreeA F B :=
  match a with
  | Pure x   => Pure (g x)
  | MkAp h x => MkAp (fmap (fun k : _ -> A => g \o k) h) x  
  end.

Program Instance FreeA_Functor (F : Type -> Type)
  `{Functor F} : Functor (FreeA F) := {
  fmap := fun _ _ f x => FreeA_map f x
}.

Import FunctorLaws.

Lemma fmap_rewrite_compose {A B C : Type} `{Functor F} :
  forall (f : B -> C) (g : A -> B) (x : F A), 
    fmap f (fmap g x) = (fmap f \o fmap g) x.
Proof.
  intros f g x.
  reflexivity.
Qed.

Program Instance FreeA_FunctorLaws `{FunctorLaws F} : FunctorLaws (FreeA F).
(* Theorem FreeA_Functor_law1 {A : Type} *)
(*         `{Functor F} `{FunctorLaws F} : *)
(*   forall (x : FreeA F A), fmap id x = id x. *)
Obligation 1.
Proof.
extensionality x.
revert x.
induction x; simpl in *; trivial.
- now rewrite fmap_id.
Defined.
Obligation 2.
extensionality x.
induction x; simpl in *; trivial.
- f_equal.
  rewrite fmap_rewrite_compose.
  now rewrite fmap_comp.
Defined.

Fixpoint FreeA_depth {A : Type} `{Functor F}
         (x : FreeA F A) : nat :=
  match x with
  | Pure a   => O
  | MkAp _ y => S (FreeA_depth y)
  end.

Lemma FreeA_fmap_preserves_depth {A B : Type} `{Functor F} :
  forall (x : FreeA F A) (f : A -> B),
  FreeA_depth (FreeA_map f x) = FreeA_depth x.
Proof.
  induction x; trivial.
Qed.

From Equations Require Import Equations.

Equations FreeA_ap {A B : Type} `{Functor F}
         (k : FreeA F (A -> B)) (y : FreeA F A) : FreeA F B by wf (FreeA_depth k) :=
FreeA_ap (Pure g) y := g <$> y;
FreeA_ap (MkAp h x) y := MkAp (fmap uncurry h) (FreeA_ap (fmap pair x) y).
Obligation 1.
Proof.
  rewrite FreeA_fmap_preserves_depth. auto.
Defined.
Transparent FreeA_ap_unfold.

Program Instance FreeA_Applicative
  `{Functor F} : Applicative (FreeA F) := {
  pure _ x := Pure x;
  ap _ _ k y := FreeA_ap k y
}.

Import ApplicativeLaws.

Print FreeA_ind.

Lemma lemma1_pure {A B C : Type} `{Functor F} `{FunctorLaws F} :
  forall (u : B -> C) (f : A -> B) (x : FreeA F A),
    fmap u (Pure f <*> x) = fmap (fun k : A -> B => u \o k) (Pure f) <*> x.
Proof.
  intros u f x.
  simpl "<*>".
  repeat rewrite FreeA_ap_equation_1.
  now rewrite <- fmap_comp.
Qed.

Lemma uncurry_l_1 {A B C : Type} :
  forall (f : A -> B -> C) (g : A * B -> C) (x : A) (y : B),
    f x y = g (pair x y) -> (uncurry f) (pair x y) = g (pair x y).
Proof.
  intros f g x y H.
  unfold uncurry. simpl. apply H.
Qed.

Lemma lemma1_ap {A B C b : Type} `{Functor F} `{FunctorLaws F} :
  forall (u : B -> C) (v : FreeA F b) (f : F (b -> A -> B)) (x : FreeA F A), 
         (* (IH : forall (g : FreeA F (b -> A -> B)), fmap u (g <*> v) = fmap (fun k : A -> B => u \o k) g <*> v), *)
    fmap u (MkAp f v <*> x) = fmap (fun k : A -> B => u \o k) (MkAp f v) <*> x.
Proof.
  intros u v f x.
  simpl "<*>".
  repeat rewrite (FreeA_ap_equation_2). simpl.
  (* Peel of the MkAp constructor *)
  f_equal.
  (* Now we need to use f_equal again to get read of the outer fmap [ F],
     but first we need to massage the fmap's arguments in a form that uses explicit
     function composition \o.*) 
  remember (fun k : b * A -> B => u \o k) as p.
  remember (fun k : b -> A -> B => (fun k0 : A -> B => u \o k0) \o k) as q.
  assert (Htemp: fmap[ F] uncurry (fmap[ F] q f) = fmap[ F] (uncurry \o q) f).
  { now rewrite <- fmap_comp. } rewrite Htemp. clear Htemp.
  assert (Htemp : fmap[ F] p (fmap[ F] uncurry f) = fmap[ F] (p \o uncurry) f).
  { now rewrite <- fmap_comp. } rewrite Htemp. clear Htemp.
  f_equal.
  extensionality z.
  (* Now we need to prove (p \o uncurry) = (uncurry \o q), which, I suppose, should be
     our inductive hypothesis (if we actually did induction). *)
Admitted.

(* ∀g :: f (y → a), u :: FreeA f x. *)
(* fmap ( ◦ h) g :$: u ≡ g :$: fmap h  *)
Lemma lemma1 {A B C : Type} `{Functor F} :
  forall (u : B -> C) (v : FreeA F (A -> B)) (x : FreeA F A),
    fmap u (v <*>x) = fmap (fun k : A -> B => u \o k) v <*> x.
Proof.
  intros u v x.
  destruct v.
  - simpl. admit.
  - intros.
  induction v.
  pose (Statement := fun (v0 : FreeA F (A -> B)) =>
    forall x : FreeA F A,
    fmap u (v0 <*> x) =
    fmap (fun k : A -> B => u \o k) v0 <*> x
       ).
  Locate "<**>".
  Check (FreeA_ind F Statement).
  induction v.
Admitted.

Program Instance FreeA_ApplicativeLaws
  `{FunctorLaws F} :
  ApplicativeLaws (FreeA F).
Obligation 1.
(* ap_id *)
(* ap (pure id) = id *)
(* FreeA_ap (Pure id) y) = idtac *)
extensionality y.
induction y.
- reflexivity.
- rewrite FreeA_ap_equation_1.
  now rewrite fmap_id.
Defined.
Obligation 2.
(* ap_comp : forall (a b c : TYpe) (v : f (a -> b)) (u : f (b -> c)) (w : f a), *)
(*     pure (fun f g x => f (g x)) <*> u <*> v <*> w = u <*> (v <*> w); *)
(* FreeA_ap *)
(*   (FreeA_ap (FreeA_ap (Pure (fun f g x => f (g x))) u) v) w = *)
(* FreeA_ap u (FreeA_ap v w) *)
rewrite FreeA_ap_equation_1.
(* remember (fmap[ FreeA F] (fun (f : b -> c) (g : a -> b) (x : a) => f (g x)) u) as t. *)
induction w.
- simpl. 
Obligation 4.
admit.

  
(* pose (goal := fun u => FreeA_ap u (Pure y) = FreeA_ap (Pure (fun f : a -> b => f y)) u). *)
(* refine (FreeA_ind F goal _ _). *)








