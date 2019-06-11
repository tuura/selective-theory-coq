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

Program Instance Select_Functor (F : Type -> Type) : Functor (Select F) := {
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

Program Instance Select_FunctorLaws : FunctorLaws (Select F).
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
  rewrite <- H.
  now rewrite IHx.
Qed.

(* This is a helper function used in the Select_selectBy definition *)
Definition g {A B C D E : Type}
           (f : A -> ((B -> C) + C))
           (a : A) :
  (((D -> B) + B) -> ((D -> C) + C)) + (E + C) :=
  match f a with
  | inr r => Right (Right r)
  | inl l => Left  (Either_bimap (fun k => l \o k) l)
  end.

Equations Select_selectBy {A B C : Type} {F : Type -> Type}
          (f : A -> ((B -> C) + C))
          (x : Select F A)
          (a : Select F B) : Select F C :=
Select_selectBy f x (Pure y)       := (either (fun k => k y) id \o f) <$> x;
Select_selectBy f x (MkSelect y z) := MkSelect (Select_selectBy (g f) x y) z.

Definition Select_select {A B : Type} {F : Type -> Type}
           (x : Select F (A + B))
           (handler : Select F (A -> B)) : Select F B :=
  Select_selectBy (mapLeft (fun x f => f x)) x handler.

(* select (Left <$> f) (flip ($) <$> x) *)
Definition Select_ap {A B : Type} {F : Type -> Type}
           (f : Select F (A -> B)) (x : Select F A) : Select F B :=
  Select_select (Left <$> f) ((fun x f => f x) <$> x).

Program Instance Select_Applicative
        (F : Type -> Type) : Applicative (Select F) :=
  { is_functor := Select_Functor F
  ; pure _ x := Pure x
  ; ap _ _ f x := Select_ap f x
}.

Program Instance Select_Selective
        (F : Type -> Type) : Selective (Select F) :=
  { is_applicative := Select_Applicative F
  ; select _ _ x f := Select_select x f
}.

Import ApplicativeLaws.

Program Instance Select_ApplicativeLaws `{FunctorLaws F} : ApplicativeLaws (Select F).
Obligation 1.
Admitted.
Obligation 2.
Admitted.
Obligation 4.
Admitted.
Obligation 5.
Admitted.

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

Require Import Coq.Program.Equality.
Print JMeq.

Lemma id_is_unique_2 :
  forall (A B : Type) (f : A -> A) (g : B -> B),
  f ~= g.
Proof.
  intros A B f g.
  rewrite (id_is_unique A f).
  rewrite (id_is_unique B g).
Admitted.

Lemma subst_id :
  forall (A B : Type) (body : (A -> A) -> B),
  (fun f : A -> A => body f) = const (body id).
Proof.
  intros A B body.
  extensionality f.
  now rewrite (@id_is_unique A f).
Qed.

Lemma eta_expand :
  forall (A B : Type) (body : A -> B),
  body = (fun arg : A => body arg).
Proof. trivial. Qed.

(* Lemma left_id_is_id {A : Type} : *)
(*   forall (f : A -> A) (x : (A -> A) + A), *)
(*   x = inl (B := A) f -> either (fun y => f y) id = id. *)

(* -- P2 (does not generally hold): select (pure (Left x)) y = ($x) <$> y *)
(* p2 :: Selective f => a -> f (a -> b) -> f b *)
(* p2 x y = select (pure (Left  x)) y === y <*> pure x *)
Theorem Select_pure_left {F : Type -> Type} :
  forall (A B : Type) (x : A) (y : Select F (A -> B)),
    select (pure (Left x)) y = (fun f => f x) <$> y.
Admitted.

(* -- P3 (does not generally hold): select (pure (Right x)) y = pure x *)
(* p3 :: Selective f => b -> f (a -> b) -> f b *)
(* p3 x y = select (pure (Right x)) y === pure x *)
Theorem Select_pure_right {F : Type -> Type} :
  forall (A B : Type) (x : B) (y : Select F (A -> B)),
    select (pure (Right x)) y = Pure x.
Admitted.

(* -- F2 (Free): select (first f <$> x) y = select x ((. f) <$> y) *)
(* f2 :: Selective f => (a -> c) -> f (Either a b) -> f (c -> b) -> f b *)
(* f2 f x y = select (first f <$> x) y === select x ((. f) <$> y) *)
Theorem Select_free_2 {F : Type -> Type} :
  forall (A B C : Type) (f : A -> C) (x : Select F (A + B)) (y : Select F (C -> B)),
    select (mapLeft f <$> x) y = select x ((fun g : C -> B => g \o f) <$> y).
Admitted.

Theorem Select_Selective_law1 {F : Type -> Type} :
  forall (A : Type) (x : Select F (A + A)),
    select x (Pure id) = either id id <$> x.
Proof.
  intros A x.
  simpl select.
  unfold Select_select.
  rewrite Select_selectBy_equation_1.
  f_equal.
  unfold comp.
  extensionality x0.
  destruct x0; trivial.
Qed.

Lemma Select_map_comp :
  forall (A B C : Type) (F : Type -> Type) (f : B -> C) (g : A -> B) (x : Select F A),
    Select_map f (Select_map g x) = Select_map (f \o g) x.
Proof.
  intros A B C F f g x.
  remember (fmap_comp A B C f g) as H.
  simpl fmap in H.
Admitted.

Lemma sequence_ap `{Applicative F} :
  forall (A B : Type) (p : F A) (q : F B),
    p *> q = (const id) <$> p <*> q.
Proof.
  intros A B p q.
  reflexivity.
Qed.

(* -- D1 (distributivity): pure x <*? (y *> z) = (pure x <*? y) *> (pure x <*? z) *)
(* d1 :: Selective f => Either a b -> f (a -> b) -> f (a -> b) -> f b *)
Theorem Select_Selective_law2 {F : Type -> Type} {H: ApplicativeLaws (Select F)} :
  forall (A B : Type) (x : A + B) (y : Select F (A -> B)) (z : Select F (A -> B)),
    select (Pure x) (y *> z) = (select (Pure x) y) *> (select (Pure x) z).
Proof.
  intros A B x y z.
  destruct x.
  - repeat rewrite Select_pure_left.
    repeat rewrite sequence_ap.
    assert (fmap[ Select F] (const id) (fmap[ Select F] (fun f : A -> B => f a) y) <*>
                  fmap[ Select F] (fun f : A -> B => f a) z =
            (fmap[ Select F] (const id) \o fmap[ Select F] (fun f : A -> B => f a)) y <*>
                  fmap[ Select F] (fun f : A -> B => f a) z).
    { reflexivity. }
    rewrite H0. clear H0.
    rewrite fmap_comp.
    unfold comp.
    unfold const.
    rewrite <- ap_fmap.
    assert (fmap[ Select F] (fun _ : A -> B => id) y <*> fmap[ Select F] (fun f : A -> B => f a) z =
            fmap[ Select F] (fun _ : A -> B => id) y <*> (pure[ Select F] (fun f : A -> B => f a) <*> z)).
    { now rewrite ap_fmap. }
    
    rewrite <- ap_fmap.
    assert (fmap[ Select F] (fun f : A -> B => f a) (fmap[ Select F] (fun _ : A -> B => id) y <*> z) =
            fmap[ Select F] (fun f : A -> B => f a) ((fmap[ Select F] (fun _ : A -> B => id) y) <*> z)).
    assert ((const id \o (fun f : A -> B => f a)) =
            )

    assert (fmap[ Select F] (const  id) (fmap[ Select F] (fun f : A -> B => f a) y) =
            (fmap[ Select F] (const (@id A)) \o fmap[ Select F] (fun f : A -> B => f a)) y).
    {reflexivity. }
    rewrite H0. clear H0.

(* -- D1 (distributivity): pure x <*? (y *> z) = (pure x <*? y) *> (pure x <*? z) *)
(* d1 :: Selective f => Either a b -> f (a -> b) -> f (a -> b) -> f b *)
Theorem Select_Selective_law2 {F : Type -> Type} {H: ApplicativeLaws (Select F)} :
  forall (A B : Type) (x : A + B) (y : Select F (A -> B)) (z : Select F (A -> B)),
    select (Pure x) (y *> z) = (select (Pure x) y) *> (select (Pure x) z).
Proof.
  intros A B x y z.
  destruct x.
  - repeat rewrite Select_pure_left.
    assert (fmap[ Select F] (fun f : A -> B => f a) (y *> z) =
            fmap[ Select F] (fun f : A -> B => f a) ((const id) <$> y <*> z)).
    { reflexivity. }
    rewrite H0. clear H0.
    assert ((fmap[ Select F] (const id) y <*> z) = pure (const id) <*> y <*> z).
    { now rewrite ap_fmap. }
    rewrite H0. clear H0.
    assert (fmap[ Select F] (fun f : A -> B => f a) ((pure[ Select F]) (const id) <*> y <*> z) =
            pure[ Select F] (fun f : A -> B => f a) <*> (pure[ Select F] (const id) <*> y <*> z)).
    { simpl.
      unfold Select_ap at 3.
      simpl.
      rewrite Select_map_equation_1.
      remember (@Select_pure_left F) as H_pure_left.
      simpl select in H_pure_left.
      rewrite H_pure_left.
      simpl.
      rewrite Select_map_comp.
      unfold comp.
      reflexivity. }
    rewrite H0. clear H0.
    (* assert ((pure[ Select F]) (const id) <*> y <*> z = ((pure[ Select F]) (fun f : A -> B => id) <*> y) <*> z). *)
    (* { reflexivity. } *)
    (* rewrite H0. clear H0. *)

    (* assert (((pure[ Select F]) (fun f : A -> B => id) <*> y) <*> z = *)
    (*         (y <*> (pure[ Select F]) id) <*> z). *)

    assert (fmap[ Select F] (fun f : A -> B => f a) y *> fmap[ Select F] (fun f : A -> B => f a) z =
            (pure (fun f : A -> B => f a) <*> y) *> fmap[ Select F] (fun f : A -> B => f a) z).
    { now rewrite ap_fmap. }
    rewrite H0. clear H0.
    assert (fmap[ Select F] (fun f : A -> B => f a) z =
            (pure (fun f : A -> B => f a) <*> z)).
    { now rewrite ap_fmap. }
    rewrite H0. clear H0.
    remember ( (pure[ Select F]) (fun f : A -> B => f a) <*> y ) as p.
    remember ( (pure[ Select F]) (fun f : A -> B => f a) <*> z ) as q.
    assert (p *> q = (const id) <$> p <*> q).
    {reflexivity. }
    rewrite H0. clear H0.
    assert (fmap[ Select F] (const id) p <*> q = (pure (const id) <*> p) <*> q).
    { now rewrite ap_fmap. }
    rewrite H0. clear H0.
    rewrite Heqp. rewrite Heqq. clear Heqp p Heqq q.
    remember ((pure[ Select F]) (const id) <*> ((pure[ Select F]) (fun f : A -> B => f a) <*> y)) as r.
    rewrite <- ap_comp at 0.
    assert (r <*> ((pure[ Select F]) (fun f : A -> B => f a) <*> z) =
            pure comp <*> r <*> (pure[ Select F]) (fun f : A -> B => f a) <*> z).
    assert (((pure[ Select F]) (const (@id A)) <*> ((pure[ Select F]) (fun f : A -> B => f a) <*> y)) =
            (pure[ Select F] (const (@id A))
                  <*> pure[ Select F] (fun f : A -> B => f a)
                  <*> y)).

    assert ((pure[ Select F]) (const id) <*> ((pure[ Select F]) (fun f : A -> B => f a) <*> y) <*>
                              ((pure[ Select F]) (fun f : A -> B => f a) <*> z) =
            ((pure[ Select F]) (const id) <*> ((pure[ Select F]) (fun f : A -> B => f a) <*> y)) <*>
                              ((pure[ Select F]) (fun f : A -> B => f a) <*> z)).
    { reflexivity. }
    (* rewrite <- ap_comp . *)
    (* rewrite ap_homo. *)

    assert ((pure[ Select F]) (const id) <*> ((pure[ Select F]) (fun f : A -> B => f a) <*> y) =
            pure (fun (f :  g => f \o g) <*> pure[ Select F] (const id) <*>
                 pure[ Select F] (fun f : A -> B => f a) <*> y).
    { reflexivity. }
    assert (fmap[ Select F] (const id) p = pure[ Select F] (const (@id A)) <*> p).
    { now rewrite ap_fmap. }
    rewrite H0. clear H0.
    assert (fmap[ Select F] (fun f : A -> B => f a) y *> fmap[ Select F] (fun f : A -> B => f a) z =
            fmap[ Select F] (fun f : A -> B => f a) )

Admitted.
      rewrite <- Select_map_comp.
      rewrite Select_pure_left.
      rewrite <- (@ap_fmap (Select F)).

    assert (fmap[ Select F] (fun f : A -> B => f a) y = pure (fun f : A -> B => f a) <*> y).
    { rewrite ap_fmap. reflexivity. }
    rewrite H0.
    assert (fmap[ Select F] (fun f : A -> B => f a) (y *> z) = pure (fun f : A -> B => f a) <*> (y *> z)).
    { rewrite ap_fmap. reflexivity. }
    rewrite H0.
    assert (y *> z = (const id) <$> y <*> z).
    { reflexivity. }
    assert ((const id) <$> y <*> z = (pure (const id)) <*> y <*> z).
    { rewrite ap_fmap. reflexivity. }
    rewrite H0.
    assert (fmap[ Select F] (fun f : A -> B => f a) (fmap[ Select F] (const id) y <*> z) =
            fmap[ Select F] ((fun f : A -> B => f a) \o (const id)) y <*> z).
    rewrite fmap_comp.
    rewrite ap_fmap.
    unfold Select_ap.
    admit.
  - repeat rewrite Select_pure_right.
    admit.
Admitted.

Definition law3_f {A B C : Type}
           (x : B + C) : B + (A + C) := Right <$> x.

Definition law3_g {A B C : Type}
           (y : A + (B -> C)) : B -> A * B + C :=
  fun a => Either_bimap (fun p => pair p a) (fun f => f a) y.

Definition law3_h  {A B C : Type}
           (z : A -> B -> C) : A * B -> C := uncurry z.

Theorem select_selective_law3_assoc
  {A B C : Type} {F : Type -> Type} `{Functor F}
  (x : Select F (B + C))
  (y : Select F (A + (B -> C)))
  (z : Select F (A -> B -> C)) :
  x <*? (y <*? z) = (law3_f <$> x) <*? (law3_g <$> y) <*? (law3_h <$> z).
Proof.
  simpl select.
  remember (@Select_free_2 F) as H_free_2.
  simpl select in H_free_2.
  unfold Select_select in H_free_2.
  unfold Select_select.
  rewrite H_free_2.
  induction z.



Lemma Select_map_comp :
  forall (A B C : Type) (F : Type -> Type) (f : B -> C) (g : A -> B) (x : Select F A),
    Select_map f (Select_map g x) = Select_map (f \o g) x.
Proof.
Admitted.

Theorem Select_Applicative_law1 {F : Type -> Type} :
  forall (A : Type),
  Select_ap (F:=F) (Pure (@id A)) = @id (Select F A).
Proof.
  intros A.
  unfold Select_ap.
  extensionality x.
  simpl fmap.
  rewrite Select_map_equation_1.
  rewrite Select_pure_left.
  simpl fmap.
  rewrite Select_map_comp.
  unfold comp.
  
  unfold select.
  unfold select.
  revert A x.
  (* Set Printing Implicit. *)
  induction x as [| A X y IH z]; trivial;
  simpl.
  rewrite Select_selectBy_equation_2.
  rewrite id_x_is_x.
  f_equal.
  rewrite <- id_x_is_x.
  (* Set Printing Implicit. *)
  rewrite <- IH.
  (* destruct y. *)
  (* - rewrite Select_selectBy_equation_1. *)
  (*   rewrite Select_selectBy_equation_1. *)
  (*   admit. *)
  (* - rewrite Select_selectBy_equation_2. *)
  (*   rewrite Select_selectBy_equation_2. *)
  remember (g inl) as p.
  remember inl as q.
    (* unfold g in Heqp. *)
  rewrite eta_expand in Heqp.
  rewrite subst_id in Heqp.
  
  unfold g in Heqp.
  rewrite bimap_id in Heqp.

  rewrite Heqp.
  rewrite Heqq.

  rewrite eta_expand in Heqq.
  rewrite subst_id in Heqq.
  rewrite Heqp.
  rewrite Heqq.
  clear IH p Heqp q Heqq.
  Unset Printing Implicit.

Program Instance Select_ApplicativeLaws `{FunctorLaws F} : ApplicativeLaws (Select F).
Obligation 1.
  extensionality x.
  unfold Select_ap.
  revert F H H0 a x.
  Set Printing Implicit.
  induction x.
  - trivial.
  - rewrite Select_selectBy_equation_2.
    rewrite id_x_is_x.
    f_equal.
    rewrite <- id_x_is_x.
    rewrite <- IHx.
    remember (g inl) as p.
    remember inl as q.
    assert (p id = q id).
    { rewrite Heqp. rewrite Heqq. unfold g. now rewrite bimap_id. }
    rewrite eta_expand in Heqp.
    rewrite subst_id in Heqp.
    rewrite eta_expand in Heqq.
    rewrite subst_id in Heqq.
    unfold g in Heqp.
    rewrite bimap_id in Heqp.
    rewrite Heqp.
    rewrite Heqq.
    Unset Printing Implicit.


Program Instance Select_ApplicativeLaws `{FunctorLaws F} : ApplicativeLaws (Select F).
Obligation 1.
  extensionality x.
  unfold Select_ap.
  revert a x.
  induction x; trivial.
  - rewrite Select_selectBy_equation_2.
    rewrite id_x_is_x.
    f_equal.
    rewrite <- id_x_is_x.
    rewrite <- IHx.
    remember (g inl) as p.
    remember inl as q.
    assert (p id = q id).
    { rewrite Heqp. rewrite Heqq. unfold g. now rewrite bimap_id. }
    rewrite eta_expand in Heqp.
    rewrite subst_id in Heqp.
    rewrite eta_expand in Heqq.
    rewrite subst_id in Heqq.
    unfold g in Heqp.
    rewrite bimap_id in Heqp.
    rewrite Heqp.
    rewrite Heqq.
    Set Printing Implicit.
    reflexivity.
    rewrite subst_id in Heqp.
    assert (Either_bimap (Y:=A) (fun k : X -> A => id \o k) id = id).
    { extensionality y.
      destruct y; trivial. }
    rewrite H1 in Heqp.
    rewrite Heqp.
    remember inl as q.
    (* assert (t = (fun b : (X -> A) + A -> (X -> A) + A => inl b)).  *)
    assert (Either_bimap (Y:=A) (fun k : X -> A => id \o k) id = id).
    { extensionality y.
      destruct y; trivial. }
    assert (fun (a : A -> A) => Either_bimap (fun k : X -> A => a \o k) a = a).
    { extensionality y.
      destruct y; trivial. }
    Check (g inl).
    unfold g.
    Check (fun a : A -> A => Either_bimap (fun k : X -> A => a \o k) a).

    assert (forall X Y, inl = (fun (x : X) => @inl X Y x)).
    { reflexivity. }
    rewrite H1 in IHx.
    remember ((fun a : A -> A => inl (Either_bimap (fun k : X -> A => a \o k) a))) as t.
    (* Looks like we're stuck; the gool here looks like this: *)
    (* IHx : Select_selectBy inl (Pure id) x = id x *)
    (* ============================ *)
    (* Select_selectBy (g inl) (Pure id) x = x *)
    (* We need to prove the following assertion: *)
    (* assert (g inl = inl). *)
    (* But it doesn't typecheck *)
Admitted.
Obligation 2.
Admitted.
(* Interchange *)
(* u <*> pure y = pure ($ y) <*> u *)
Obligation 5.
extensionality x.
unfold Select_ap.
revert a b f x.
induction x; trivial.
- rewrite Select_selectBy_equation_2.
  rewrite Select_map_equation_2.
  f_equal.
  remember (Either_bimap (fun k : X -> A => f \o k) f) as t.
  rewrite <- (IHx ((Either_bimap (fun k : X -> A => f \o k) f))). 
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

