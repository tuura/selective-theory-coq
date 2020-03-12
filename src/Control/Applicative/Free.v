Require Import Reasoning.
Require Import Hask.Control.Iso.
Require Import Hask.Prelude.
Require Import Data.Either.
Require Import Data.Monoid.
Require Import Data.Functor.
Require Import Data.Functor.Contravariant.
Require Import Control.Applicative.
(* Require Import Data.Over. *)
Require Import Coq.Strings.String.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Classes.Morphisms_Prop.
Require Import FunctionalExtensionality.

Set Universe Polymorphism.

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
Inductive FreeA (f : Set -> Set) (a : Set) :=
    Pure : a -> FreeA f a
  | MkAp : forall b, f (b -> a) -> FreeA f b -> FreeA f a.

Arguments Pure {f} {a}.
Arguments MkAp {f} {a} {b}.

Check FreeA_ind.

Fixpoint FreeA_map {A B : Set} `{Functor F}
           (g : (A -> B)) (a : FreeA F A) : FreeA F B :=
  match a with
  | Pure x   => Pure (g x)
  | MkAp h x => MkAp (fmap (fun k : _ -> A => g \o k) h) x
  end.

Program Instance FreeA_Functor (F : Set -> Set)
  (HF : Functor F) : Functor (FreeA F) := {
  fmap := fun _ _ f x => FreeA_map f x
}.

Import FunctorLaws.

Lemma fmap_rewrite_compose {A B C : Set} `{Functor F} :
  forall (f : B -> C) (g : A -> B) (x : F A),
    fmap f (fmap g x) = (fmap f \o fmap g) x.
Proof.
  intros f g x.
  reflexivity.
Qed.

Program Instance FreeA_FunctorLaws
  (F : Set -> Set) (HF : Functor F) (HFL : FunctorLaws F) : FunctorLaws (FreeA F).
(* Theorem FreeA_Functor_law1 {A : Set} *)
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

Fixpoint FreeA_depth {A : Set} `{Functor F}
         (x : FreeA F A) : nat :=
  match x with
  | Pure a   => O
  | MkAp _ y => S (FreeA_depth y)
  end.

Lemma FreeA_fmap_preserves_depth {A B : Set} `{Functor F} :
  forall (x : FreeA F A) (f : A -> B),
  FreeA_depth (FreeA_map f x) = FreeA_depth x.
Proof.
  induction x; trivial.
Qed.

From Equations Require Import Equations.

Equations FreeA_ap {A B : Set} `{Functor F}
         (k : FreeA F (A -> B)) (y : FreeA F A) : FreeA F B by wf (FreeA_depth k) :=
FreeA_ap (Pure g) y := g <$> y;
FreeA_ap (MkAp h x) y := MkAp (fmap uncurry h) (FreeA_ap (fmap pair x) y).
Obligation 1.
Proof.
  rewrite FreeA_fmap_preserves_depth. auto.
Defined.
Transparent FreeA_ap_unfold.

Program Instance FreeA_Applicative
  {F : Set -> Set} {HF : Functor F} : Applicative (FreeA F) := {
  pure _ x := Pure x;
  ap _ _ k y := FreeA_ap k y
}.

Import ApplicativeLaws.

Print FreeA_ind.

Lemma lemma1_pure {A B C : Set} `{Functor F} `{FunctorLaws F} :
  forall (u : B -> C) (f : A -> B) (x : FreeA F A),
    fmap u (Pure f <*> x) = fmap (fun k : A -> B => u \o k) (Pure f) <*> x.
Proof.
  intros u f x.
  simpl "<*>".
  repeat rewrite FreeA_ap_equation_1.
  now rewrite <- fmap_comp.
Qed.

Lemma uncurry_l_1 {A B C : Set} :
  forall (f : A -> B -> C) (g : A * B -> C) (x : A) (y : B),
    f x y = g (pair x y) -> (uncurry f) (pair x y) = g (pair x y).
Proof.
  intros f g x y H.
  unfold uncurry. simpl. apply H.
Qed.

Theorem FreeA_ap_fmap :
  forall (A B : Set) (F : Set -> Set) (HF : Functor F)
    (x : FreeA F A) (f : A -> B),
    pure[FreeA F] f <*> x = fmap f x.
Proof.
  intros A B F HF x f.
  induction x;
  simpl; simp FreeA_ap; now simpl.
Qed.

Module FreeA_Parametricity.
Import ContravariantLaws.

Inductive F1 (F : Set -> Set) (A X : Set) := MkF1 : F (X -> A) -> F1 F A X.

Program Instance F1_Contravariant
  (F : Set -> Set) (HF : Functor F) (A : Set)  :
  Contravariant (F1 F A) := {
  contramap := fun _ _ h x => match x with
                           | MkF1 _ _ _ g => MkF1 F A _ (fmap (fun k => k ∘ h) g)
                           end
}.

Program Instance F1_ContravariantLaws
  (F : Set -> Set) (HF : Functor F) (HFL : FunctorLaws F) (A : Set)  :
  ContravariantLaws (F1 F A).
Obligation 1.
extensionality x.
destruct x. rewrite fmap_id. now unfold id.
Qed.
Obligation 2.
extensionality x.
destruct x. simpl. f_equal. functor_laws.
Qed.

Inductive F2 (F : Set -> Set) (A X : Set) := MkF2 : (FreeA F X -> FreeA F A) -> F2 F A X.

Program Instance F2_Contravariant
  (F : Set -> Set) (HF : Functor F) (A : Set)  :
  Contravariant (F2 F A) := {
  contramap := fun _ _ h x => match x with
                           | MkF2 _ _ _ g => MkF2 F A _ (g ∘ fmap h)
                           end
}.

Program Instance F2_ContravariantLaws
  (F : Set -> Set) (HF : Functor F) (HFL : FunctorLaws F) (A : Set)  :
  ContravariantLaws (F2 F A).
Obligation 1.
extensionality x. destruct x.
specialize (@fmap_id (FreeA F) (FreeA_Functor F HF)
                     (FreeA_FunctorLaws _ _ _)) as FreeA_map_id.
simpl in FreeA_map_id.
rewrite FreeA_map_id. unfold id. f_equal.
Qed.
Obligation 2.
extensionality x.
destruct x. simpl. f_equal.
specialize (@fmap_comp (FreeA F) (FreeA_Functor F _)
                       (FreeA_FunctorLaws _ _ _)) as FreeA_map_comp.
simpl in FreeA_map_comp.
now rewrite <- FreeA_map_comp.
Qed.

(**
  <*> is a natural transformation between contravariant functor F1 and F2
  https://arxiv.org/pdf/1403.0749.pdf (Section 4 : Parametricity)
*)
(* ∀g ::f (y → a),u ::FreeA f x. *)
(* fmap ( ◦ h) g :$:u ≡ g :$:fmap h u *)

Theorem FreeA_free_theorem :
  forall (A B X : Set) (F : Set -> Set) (HF : Functor F)
    (f : A -> B) (h : X -> B) (g : FreeA F (B -> X)) (u : FreeA F X),
    (fmap[FreeA F] (fun k => k ∘ h) g) <*> u = g <*> fmap h u.
Admitted.
Theorem FreeA_free_theorem_1 :
  forall (A B C : Set) (F : Set -> Set) (HF : Functor F)
    (f : A -> B) (g : B -> C)
    (x : FreeA F A) (y : FreeA F (A -> B)) (h : (A -> B) -> (B -> C)),
    g <$> (y <*> x) = (h <$> y) <*> (f <$[FreeA F]> x).
Admitted.

End FreeA_Parametricity.

Theorem FreeA_free_1_MkAp :
  forall (A X Y : Set) (F : Set -> Set) (HF : Functor F)
    (h : X -> Y) (g : F (Y -> A)) (u : FreeA F X),
    MkAp (fmap[F] (fun k => k ∘ h) g) u = MkAp g (fmap h u).
Admitted.

Lemma K_and_K_lemma1 :
  forall (X Y Z : Set) (F : Set -> Set) (HF : Functor F) (HFL : FunctorLaws F)
  (u : Y -> Z)
  (v : FreeA F (X -> Y))
  (x : FreeA F X),
  fmap u (v <*> x) = fmap (fmap[→_] u) v <*> x.
Proof.
  intros X Y Z F HF HFL u v x.
  destruct v as [ v | g y ].
  -`Begin
   (fmap u (pure v <*> x)).
  ≡⟨ reflexivity ⟩
   (fmap u (fmap v x)).
  ≡⟨ functor_laws ⟩
   (fmap (u ∘ v) x).
  ≡⟨ functor_laws ⟩
   ((pure (u ∘ v) <*> x)).
  ≡⟨ functor_laws ⟩
   ((fmap (fmap[→_] u) (pure v)) <*> x)
  `End.
  -`Begin
    (fmap u (MkAp y v <*> x)).
  ≡⟨ now (simpl; simp FreeA_ap) ⟩
   (MkAp (fmap (fmap[→_] u) (fmap uncurry y))
         ((pair <$> v) <*> x)).
  ≡⟨ functor_laws ⟩
   (MkAp (fmap (fmap[→_] u ∘ uncurry) y)
         ((pair <$> v) <*> x)).
  ≡⟨ f_equal ⟩
   (MkAp (fmap[ F] (uncurry ∘ (fun k => (fun g0 => u ∘ g0) ∘  k)) y)
         ((pair <$> v) <*> x)).
  ≡⟨ functor_laws ⟩
   (MkAp (fmap[ F] uncurry (fmap[ F] (fun k => (fun g0 => u ∘ g0) ∘  k) y))
         ((pair <$> v) <*> x)).
  ≡⟨ now (simpl; simp FreeA_ap) ⟩
   (fmap (fmap[→_] u) (MkAp y v) <*> x)
  `End.
Qed.

Theorem FreeA_ApplicativeLaws_composition :
  forall (A B C : Set) (F : Set -> Set) (HF : Functor F) (HFL : FunctorLaws F)
  (u : FreeA F (B -> C)) (v : FreeA F (A -> B)) (w : FreeA F A),
  pure comp <*> u <*> v <*> w = u <*> (v <*> w).
Proof.
  intros A B C F HF HFL u v w.
  generalize dependent C. generalize dependent B. generalize dependent A.
  induction w.
  - admit.
  - intros.
  `Begin
   ((pure[ FreeA F]) comp <*> u <*> v <*> MkAp f w).
  ≡⟨ functor_laws ⟩
   (((comp <$> u) <*> v) <*> MkAp f w).
  simpl. simp FreeA_ap.
  ≡⟨ admit ⟩
   (u <*> (v <*> MkAp f w))
  `End.


Theorem FreeA_ApplicativeLaws_interchange :
  forall (A B : Set) (F : Set -> Set) (HF : Functor F)
    (u : FreeA F (A -> B)) (y : A),
    u <*> pure y = pure (rev_f_ap y) <*> u.
Proof.
  intros A B F HF u y.
  destruct u as [ f | X v g ].
  - simpl. now simp FreeA_ap.
  -
  `Begin
   (MkAp v g <*> pure y).
  ≡⟨ reflexivity ⟩
   (FreeA_ap (MkAp v g) (pure y)).
  ≡⟨ now rewrite FreeA_ap_equation_2 ⟩
   (MkAp (fmap uncurry v) ((fmap pair g) <*> pure y)).
  ≡⟨ admit ⟩
   (MkAp (fmap[F] (fun k => rev_f_ap y ∘ k) v) g).
  ≡⟨ reflexivity ⟩
    (fmap (rev_f_ap y) (MkAp v g)).
  ≡⟨ now rewrite FreeA_ap_fmap ⟩
    (pure (rev_f_ap y) <*> MkAp v g)
  `End.
    simpl. simp FreeA_ap. simpl.
Lemma lemma1_ap {A B C b : Set} `{Functor F} `{FunctorLaws F} :
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
Lemma lemma1 {A B C : Set} `{Functor F} :
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
Abort.

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
generalize dependent c. generalize dependent b. generalize dependent a.
induction w.
- intros. repeat simp FreeA_ap. f_equal.
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
