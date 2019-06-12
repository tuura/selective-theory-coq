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

(* -- P1id (Identity): select x (pure id) == either id id <$> x *)
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

(* -- D1 (distributivity): pure x <*? (y *> z) = (pure x <*? y) *> (pure x <*? z) *)
(* d1 :: Selective f => Either a b -> f (a -> b) -> f (a -> b) -> f b *)
(* NB:  This law appers to be a 'theorem' if we only consider rigid selective functos. *)
(* NB2: The following proof assumes 'pure-left' and 'pure-right'. *)
Theorem Select_Selective_law2 {F : Type -> Type} {H: ApplicativeLaws (Select F)} :
  forall (A B : Type) (x : A + B) (y : Select F (A -> B)) (z : Select F (A -> B)),
    select (Pure x) (y *> z) = (select (Pure x) y) *> (select (Pure x) z).
Proof.
  intros A B x y z.
  destruct x.
  (* x is a Left *)
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
    (* rewrite <- ap_fmap. *)
    assert (fmap[ Select F] (fun _ : A -> B => id) y <*> fmap[ Select F] (fun f : A -> B => f a) z =
            fmap[ Select F] (fun _ : A -> B => id) y <*> (pure[ Select F] (fun f : A -> B => f a) <*> z)).
    { now rewrite ap_fmap. }
    rewrite H0. clear H0.
    rewrite <- ap_comp.
    assert ((pure[ Select F]) (fun (f : B -> B) (g0 : (A -> B) -> B) (x : A -> B) => f (g0 x)) <*>
             fmap[ Select F] (fun _ : A -> B => id) y <*> (pure[ Select F]) (fun f : A -> B => f a) <*> z =
            ((fmap[ Select F]) (fun (f : B -> B) (g0 : (A -> B) -> B) (x : A -> B) => f (g0 x))
              (fmap[ Select F] (fun _ : A -> B => id) y)) <*> (pure[ Select F]) (fun f : A -> B => f a) <*> z).
    { now rewrite ap_fmap. }
    rewrite H0. clear H0.
    assert (fmap[ Select F] (fun (f : B -> B) (g0 : (A -> B) -> B) (x : A -> B) => f (g0 x))
                 (fmap[ Select F] (fun _ : A -> B => id) y) =
            fmap[ Select F]
                ((fun (f : B -> B) (g0 : (A -> B) -> B) (x : A -> B) => f (g0 x)) \o (fun _ : A -> B => id))
                y).
    { now rewrite <- fmap_comp. }
    rewrite H0. clear H0.
    unfold comp.
    rewrite ap_interchange.
    remember (fun f : ((A -> B) -> B) -> (A -> B) -> B => f (fun f0 : A -> B => f0 a)) as p.
    remember (fun (_ : A -> B) (g0 : (A -> B) -> B) (x0 : A -> B) => id (g0 x0)) as q.
    assert ((pure[ Select F]) p <*> fmap[ Select F] q y <*> z =
            (fmap[ Select F]) p (fmap[ Select F] q y) <*> z).
    { now rewrite ap_fmap. }
    rewrite H0. clear H0.
    assert (fmap[ Select F] p (fmap[ Select F] q y) <*> z =
            fmap[ Select F] (p \o q) y <*> z).
    { now rewrite <- fmap_comp. }
    rewrite H0. clear H0.
    rewrite Heqp. rewrite Heqq. clear Heqp p Heqq q.
    unfold comp.
    unfold id.
    assert (fmap[ Select F] (fun f : A -> B => f a) (fmap[ Select F] (fun _ x : A -> B => x) y <*> z) =
            pure[ Select F] (fun f : A -> B => f a) <*> (fmap[ Select F] (fun _ x : A -> B => x) y <*> z)).
    { now rewrite ap_fmap. }
    rewrite H0. clear H0.
    rewrite <- ap_comp.
    remember (fun (f : (A -> B) -> B) (g0 : (A -> B) -> A -> B) (x : A -> B) => f (g0 x)) as p.
    remember (fun f : A -> B => f a) as q.
    remember (fun _ x : A -> B => x) as r.
    assert ((pure[ Select F]) p <*> (pure[ Select F]) q <*> fmap[ Select F] r y <*> z =
            ((pure[ Select F]) (p q)) <*> fmap[ Select F] r y <*> z).
    { now rewrite ap_homo. }
    rewrite H0. clear H0.
    assert ((pure[ Select F]) (p q) <*> fmap[ Select F] r y <*> z =
            (fmap[ Select F]) (p q) (fmap[ Select F] r y) <*> z).
    { now rewrite ap_fmap. }
    rewrite H0. clear H0.
    assert (fmap[ Select F] (p q) (fmap[ Select F] r y) <*> z =
            fmap[ Select F] ((p q) \o r) y <*> z).
    { now rewrite <- fmap_comp. }
    rewrite H0. clear H0.
    rewrite Heqp. rewrite Heqq. rewrite Heqr. clear Heqp r Heqq q Heqr r.
    reflexivity.
  (* x is a Right *)
  - now repeat rewrite Select_pure_right.
Qed.

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
Admitted.

(* To prove applicative laws we, again, must (?) assume pure-left *)
Theorem Select_Applicative_law1 {F : Type -> Type} :
  forall (A : Type),
  Select_ap (F:=F) (Pure (@id A)) = @id (Select F A).
Proof.
  intros A.
  unfold Select_ap.
  extensionality x.
  simpl fmap.
  rewrite Select_map_equation_1.
  remember (Select_pure_left (F:=F)) as H_pure_left.
  simpl select in H_pure_left. 
  rewrite H_pure_left.
  assert (Select_map (fun (x0 : A) (f : A -> A) => f x0) x =
          fmap[ Select F] (fun (x0 : A) (f : A -> A) => f x0) x).
  { reflexivity. }
  rewrite H. clear H.
  assert ( fmap[ Select F] (fun f : (A -> A) -> A => f id) (fmap[ Select F] (fun (x0 : A) (f : A -> A) => f x0) x) =
           fmap[ Select F] ((fun f : (A -> A) -> A => f id) \o (fun (x0 : A) (f : A -> A) => f x0)) x).
  { now rewrite <- fmap_comp. }
  rewrite H. clear H.
  unfold comp.
  now rewrite fmap_id.
Qed.
