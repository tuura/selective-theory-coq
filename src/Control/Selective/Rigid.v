Require Import Coq.Program.Basics.
Require Import Hask.Prelude.
Require Import Data.Functor.
Require Import Data.Either.
Require Import Control.Applicative.
Require Import Control.Selective.
Require Import FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Classes.Morphisms_Prop.
Require Import Omega.
Require Import FunInd.
Require Import  Recdef.

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

Inductive Select (F : Type -> Type) (A : Type) :=
    Pure   : A -> Select F A
  | MkSelect : forall B, Select F (B + A) -> F (B -> A) -> Select F A.

Arguments Pure {F} {A}.
Arguments MkSelect {F} {A} {B}.

Function Select_map {A B : Type} `{Functor F}
         (f : A -> B) (x : Select F A) : Select F B :=
  match x with
  | Pure a => Pure (f a)
  | MkSelect x y => MkSelect (Select_map (fmap f) x)
                             (fmap (fun k : _ -> A => f \o k) y)
  end.

Lemma Select_map_equation_1 :
  forall (A B : Type) `(Functor F)
  (f : A -> B) (a : A),
    Select_map f (Pure a) = Pure (f a).
Proof. trivial. Qed.

Lemma Select_map_equation_2 :
  forall (A B X : Type) `(Functor F)
  (f : A -> B) (x : Select F (X + A)) (y : F (X -> A)),
    Select_map f (MkSelect x y) = MkSelect (Select_map (fmap f) x)
                                           (fmap (fun k : _ -> A => f \o k) y).
Proof. trivial. Qed.

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

Functional Scheme Select_select_help_ind := Induction for Select_select_help Sort Prop.

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
     MkSelect (Select_select (law3_f <$> x) (law3_g <$> y)) (law3_h <$> z).
Proof.
  intros A B C F H x y z.
  unfold Select_select.
  now rewrite Select_select_help_equation.
Qed.

Definition Select_ap {A B : Type} `{Functor F}
           (f : Select F (A -> B)) (x : Select F A) : Select F B :=
  Select_select (Left <$> f) (rev_f_ap <$> x).

Check Select_Functor.

Program Instance Select_Applicative
        `{Functor F} : Applicative (Select F) :=
  { is_functor := Select_Functor
  ; pure _ x := Pure x
  ; ap _ _ f x := Select_ap f x
}.

Program Instance Select_Selective
        `(H : Functor F) : Selective (Select F) :=
  { is_applicative := Select_Applicative
  ; select _ _ x f := Select_select x f
}.

Import ApplicativeLaws.

Program Instance Select_ApplicativeLaws `{Functor F} : ApplicativeLaws (Select F).
Obligation 1.
Admitted.
Obligation 2.
Admitted.
Obligation 3.
Admitted.
Obligation 4.
Admitted.
Obligation 5.
Admitted.
Obligation 6.
Admitted.

(* -- F1 (Free): f <$> select x y = select (fmap f <$> x) (fmap f <$> y) *)
(* f1 :: Selective f => (b -> c) -> f (Either a b) -> f (a -> b) -> f c *)
(* f1 f x y = f <$> select x y === select (fmap f <$> x) (fmap f <$> y) *)
Theorem Select_free_1 `{Functor F} :
  forall (A B C : Type) (f : B -> C) (x : Select F (A + B)) (y : Select F (A -> B)),
    f <$> select x y = select (fmap f <$> x)
                              ((fun g : A -> B => f \o g) <$> y).
Admitted.

(* -- F2 (Free): select (first f <$> x) y = select x ((. f) <$> y) *)
(* f2 :: Selective f => (a -> c) -> f (Either a b) -> f (c -> b) -> f b *)
(* f2 f x y = select (first f <$> x) y === select x ((. f) <$> y) *)
Theorem Select_free_2 `{Functor F} :
  forall (A B C : Type) (f : A -> C) (x : Select F (A + B)) (y : Select F (C -> B)),
    select (mapLeft f <$> x) y = select x ((fun g : C -> B => g \o f) <$> y).
Admitted.

Theorem Select_free_2_mkSelet `{Functor F} :
  forall (A B C : Type) (f : A -> C) (x : Select F (A + B)) (y : F (C -> B)),
    MkSelect (mapLeft f <$> x) y = MkSelect x ((fun g : C -> B => g \o f) <$> y).
Admitted.

(* -- F3 (Free): select x (f <$> y) = select (first (flip f) <$> x) (flip ($) <$> y) *)
(* f3 :: Selective f => (c -> a -> b) -> f (Either a b) -> f c -> f b *)
(* f3 f x y = select x (f <$> y) === select (first (flip f) <$> x) (flip ($) <$> y) *)
Theorem Select_free_3 `{Functor F} :
  forall (A B C : Type) (f : C -> A -> B)
                        (x : Select F (A + B))
                        (y : Select F C),
    select x (f <$> y) = select (mapLeft (flip f) <$> x) (rev_f_ap <$> y).
Admitted.

Theorem Select_free_3_mkSelet `{Functor F} :
  forall (A B C : Type) (f : C -> A -> B)
                   (x : Select F (A + B))
                   (y : F C),
    MkSelect x (f <$> y) = MkSelect (mapLeft (flip f) <$> x) (rev_f_ap <$> y).
Proof.
Admitted.

Lemma Select_select_to_infix :
  forall (A B : Type) `{Functor F}
  (x : Select F (A + B)%type) (y : Select F (A -> B)),
  Select_select x y = x <*? y.
Proof. reflexivity. Qed.

Lemma Select_map_to_fmap :
  forall (A B : Type) `{Functor F}
  (x : Select F A) (f : A -> B),
  Select_map f x = fmap f x.
Proof. reflexivity. Qed.

Require Import Coq.Program.Equality.

Functional Scheme select_help_ind := Induction for Select_select_help Sort Prop.

Check select_help_ind.

Lemma Either_mapLeft_comp :
  forall (A B C D : Type)
    (x : (A + B))
    (g : (A -> C))
    (f : (C -> D)),
    mapLeft f (mapLeft g x) = mapLeft (f \o g) x.
Proof.
  intros A B C D x f.
  destruct x; trivial.
Qed.

Lemma Either_mapLeft_right :
  forall (A B C : Type)
    (x : (A + B))
    (f : (A -> C)),
    mapLeft f (Either_map (@Right A B) x) = Either_map Right (mapLeft f x).
Proof.
  intros A B C x f.
  destruct x; trivial.
Qed.

(* -- P1id (Identity): select x (pure id) == either id id <$> x *)
Theorem Select_Selective_law1 `{Functor F} :
  forall (A B : Type) (x : Select F (A + B)) (y : A -> B),
    select x (Pure y) = either y id <$> x.
Proof.
  intros A B x y.
  simpl select.
  rewrite Select_select_equation_1.
  f_equal.
  unfold comp.
  destruct x; trivial.
Qed.

(* p2 :: Selective f => a -> f (a -> b) -> f b *)
(* p2 x y = select (pure (Left  x)) y === y <*> pure x *)
(* This theorem can be proved for any rigid selective functor, i.e. if apS = (<*>) *)
Theorem Select_pure_left `{HF : Functor F} {HFL : FunctorLaws F} :
  forall (A B : Type) (x : A) (y : Select F (A -> B)),
    select (pure (Left x)) y = (rev_f_ap x) <$> y.
Proof.
  intros A B x y.
  (* The idea of the proof is to massage the goal into the form of the definition of Select_ap,
     fold the definition, substitute it with the applicative <*> and finish the prove using
     the Applicative laws. *)

  (* First, we use fmap_id to append an id application to the second argument of select *)
  assert ( select (pure (inl x)) y =
           select (pure (inl x)) (fmap id y)) as H.
  { now rewrite fmap_id. } 
  rewrite H. clear H.
  (* Now we use the third Selective Free Theorem to transfer the newly created id to the first argument
     of select and leave the second fmap'ed by the reverse function application *)
  rewrite Select_free_3.
  (* Drag the id inside Pure *)
  remember (fmap[ Select F] (mapLeft (flip id)) (pure (inl x))) as p.
  compute in Heqp.
  rewrite Heqp. clear Heqp p.
  (* Use ap_homo to extract inl (aka Left) from Pure *)
  assert (Pure (inl (fun x0 : A -> B => x0 x)) <*? fmap[ Select F] rev_f_ap y =
          pure inl <*> pure (fun x0 : A -> B => x0 x) <*? fmap[ Select F] rev_f_ap y) as H.
  { now rewrite ap_homo. }
  rewrite H. clear H.
  (* Use ap_fmap to rewrite `pure inl <*>` as `inl <$>` *) 
  assert (pure inl <*> pure (fun x0 : A -> B => x0 x) <*? fmap[ Select F] rev_f_ap y =
          inl <$> pure (fun x0 : A -> B => x0 x) <*? fmap[ Select F] rev_f_ap y) as H.
  { now rewrite ap_fmap. }
  rewrite H. clear H.
  (* Fold reverse function application *)
  assert (inl <$> pure (fun x0 : A -> B => x0 x) <*? fmap[ Select F] rev_f_ap y =
          inl <$> pure (rev_f_ap x) <*? fmap[ Select F] rev_f_ap y) as H.
  { reflexivity. }
  rewrite H. clear H.
  (* Unfold <*? to make the goal identical to Select_ap definition *)
  remember (pure (rev_f_ap x)) as g.
  simpl "<*?".
  rewrite Select_map_to_fmap.
  assert (Select_select (fmap[ Select F] inl g) (Select_map rev_f_ap y) =
          Select_ap g y).
  { reflexivity. }
  rewrite H. clear H.
  (* Use the rigidness of the freer selective construction, i.e. the fact that
     Select_ap == apS == (<*>) *)
  assert (Select_ap g y = g <*> y).
  { reflexivity. }
  rewrite H. clear H.
  rewrite Heqg. clear Heqg g.
  (* Now the proof can be finished using the Applicative law ap_fmap *)
  now rewrite ap_fmap.
Qed.

Definition reassoc_triple {A B C : Type}
    (p : (A * (B * C))) : (A * B * C) :=
  match p with
  | pair x (pair y z) => pair (pair x y) z
  end.

(* The associativity law proof for now gets stuck in the inductive case.*)
Theorem Select_Selective_law3_assoc :
  forall (A B C : Type) `{FunctorLaws F}
  (x : Select F (B + C))
  (y : Select F (A + (B -> C)))
  (z : Select F (A -> B -> C)),
  x <*? (y <*? z) = (law3_f <$> x) <*? (law3_g <$> y) <*? (law3_h <$> z).
  (* Select_select x (Select_select y z) = *)
  (* Select_select (Select_select (Select_map law3_f x) (Select_map law3_g y)) (Select_map law3_h z). *)
Proof.
  dependent induction z.
  - remember (y <*? Pure a) as p.
    simpl "<*?" in Heqp.
    rewrite Select_select_equation_1 in Heqp.
    rewrite Select_map_to_fmap in Heqp.
    rewrite Heqp. clear Heqp p.
    remember (fmap[ Select F] law3_h (Pure a)) as p.
    simpl fmap in Heqp.
    rewrite Heqp. clear Heqp p.
    remember (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y) as q.
    remember ( q <*? Pure (law3_h a)) as p.
    simpl "<*?" in Heqp.
    rewrite Select_select_equation_1 in Heqp.
    rewrite Select_map_to_fmap in Heqp.
    rewrite Heqp. clear Heqp p.
    (* rewrite Select_free_3 in Heqq. *)
    rewrite Heqq. clear Heqq q.
    remember (fmap[ Select F] (either (law3_h a) id)
                  (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y)) as p.
    rewrite Select_free_1 in Heqp.
    repeat rewrite fmap_comp_x in Heqp.
    rewrite Select_free_3 in Heqp.
    rewrite Heqp. clear Heqp p.
    remember (x <*? fmap[ Select F] (either a id) y) as p.
    rewrite Select_free_3 in Heqp.
    rewrite Heqp. clear Heqp p.
    f_equal.
    f_equal.
    + f_equal. f_equal.
      extensionality z. destruct z; trivial.
    +
      revert x y a.
      (* subst T1. *)
      (* dependent induction x generalizing A B C y. *)
      dependent destruction x.
      * intros x a0.
        simpl fmap.
        f_equal.
        destruct a; now compute.
      * intros y a.
        simpl fmap in *. f_equal.
        ** unfold law3_h. unfold law3_f.
           assert ((fun y0 : B + C => Either_map (either (uncurry a) id) (fmap[ sum B] inr y0)) =
                   (fun y0 : B + C => fmap (either (uncurry a) id) (fmap[ sum B] inr y0))) as H1.
           { reflexivity. }
           rewrite H1. clear H1.
           assert ((fun y0 : B + C => fmap (either (uncurry a) id) (fmap[ sum B] inr y0)) =
                   (fun y0 : B + C => fmap (either (uncurry a) id \o inr) y0)) as H1.
           { now rewrite <- fmap_comp. }
           rewrite H1. clear H1.
           assert ((fun y0 : B + C => fmap (either (uncurry a) id \o inr) y0) =
                   (fun y0 : B + C => fmap id y0)) as H1.
           { extensionality y0. destruct y0; now compute. }
           rewrite H1. clear H1.
           setoid_rewrite fmap_id.
           assert ((@Either_map  B0 (B + C) (B + C) id) = id) as H1.
           { extensionality z. destruct z; trivial. }
           rewrite H1. clear H1.
           rewrite Select_map_to_fmap.
           rewrite fmap_id. now unfold id.
        ** unfold law3_h. unfold law3_f.
           assert ((fun y0 : B + C => Either_map (either (uncurry a) id) (fmap[ sum B] inr y0)) =
                   (fun y0 : B + C => fmap (either (uncurry a) id) (fmap[ sum B] inr y0))) as H1.
           { reflexivity. }
           rewrite H1. clear H1.
           assert ((fun y0 : B + C => fmap (either (uncurry a) id) (fmap[ sum B] inr y0)) =
                   (fun y0 : B + C => fmap (either (uncurry a) id \o inr) y0)) as H1.
           { now rewrite <- fmap_comp. }
           rewrite H1. clear H1.
           assert ((fun y0 : B + C => fmap (either (uncurry a) id \o inr) y0) =
                   (fun y0 : B + C => fmap id y0)) as H1.
           { extensionality y0. destruct y0; now compute. }
           rewrite H1. clear H1.
           setoid_rewrite fmap_id.
           assert ((fun k : B0 -> B + C => id \o k) = id) as H1.
           { extensionality k. trivial. }
           rewrite H1. clear H1.
           rewrite fmap_id. now unfold id. 
  - remember (x <*? (y <*? MkSelect z f)) as lhs.
    remember (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y <*? fmap[ Select F] law3_h (MkSelect z f)) as rhs.
    simpl in *.
    rewrite Select_select_equation_2 in Heqlhs.
    rewrite Select_select_equation_2 in Heqlhs.
    rewrite Select_select_equation_2 in Heqrhs.
    repeat rewrite Select_select_to_infix in *. repeat rewrite Select_map_to_fmap in *.
    repeat rewrite Either_map_to_fmap in *.
    rewrite Heqlhs. rewrite Heqrhs. clear Heqlhs lhs Heqrhs rhs.
    repeat rewrite fmap_comp_x.
    remember (MkSelect
    (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g (fmap[ Select F] law3_f y <*? fmap[ Select F] law3_g z))
    (fmap[ F] (fun y0 : B0 -> A -> B -> C => law3_h (law3_h y0)) f)) as lhs.
    remember (MkSelect
    (fmap[ Select F] law3_f (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y) <*?
     fmap[ Select F] (fun y0 : B0 + (A -> B -> C) => law3_g (fmap[ sum B0] law3_h y0)) z)
    (fmap[ F] (fun y0 : B0 -> A -> B -> C => law3_h (law3_h \o y0)) f)) as rhs.
    rewrite Select_free_3_mkSelet in Heqlhs.
    rewrite Select_free_3_mkSelet in Heqrhs.
    remember (fun y0 : B0 -> A -> B -> C => law3_h (law3_h \o y0)) as t.
    assert (t = fun (y0 : B0 -> A -> B -> C) => (law3_h (law3_h y0)) \o reassoc_triple).
    { rewrite Heqt. extensionality y0. extensionality p. destruct p. destruct p; trivial. }
    rewrite H1 in Heqrhs. clear H1 Heqt t.
    Check ((mapLeft (flip (fun y0 : B0 -> A -> B -> C => law3_h (law3_h y0))))).
    assert ((flip (fun y0 : B0 -> A -> B -> C => law3_h (law3_h y0))) =
            ((fun (p : B0 * A * B) (y0 : B0 -> A -> B -> C) => law3_h (law3_h y0) p))) by reflexivity.
    rewrite H1 in Heqlhs. clear H1.
    assert ((mapLeft (flip (fun y0 : B0 -> A -> B -> C => law3_h (law3_h y0) \o reassoc_triple))) =
            (mapLeft (b:=C) (fun (p : B0 * (A * B)) (y0 : B0 -> A -> B -> C) => (law3_h (law3_h y0) \o reassoc_triple) p)))
      by reflexivity.
    rewrite H1 in Heqrhs. clear H1.
    assert ((mapLeft (b := C)
                   (fun (p : B0 * (A * B)) (y0 : B0 -> A -> B -> C) => (law3_h (law3_h y0) \o reassoc_triple) p)) =
            (mapLeft (fun (p : B0 * A * B) (y0 : B0 -> A -> B -> C) => law3_h (law3_h y0) p)) \o
             mapLeft reassoc_triple).
    { extensionality q. destruct q; trivial. }
    rewrite H1 in Heqrhs. clear H1.
    remember ((fmap[ Select F] law3_f (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y) <*?
                 fmap[ Select F] (fun y0 : B0 + (A -> B -> C) => law3_g (fmap[ sum B0] law3_h y0)) z)) as t.
    rewrite <- fmap_comp in Heqrhs.
    subst t lhs rhs.
    remember (mapLeft (fun (p : B0 * A * B) (y0 : B0 -> A -> B -> C) => law3_h (law3_h y0) p)) as func_1.
    remember (fun y0 : B0 + (A -> B -> C) => law3_g (fmap[ sum B0] law3_h y0)) as t.
    unfold law3_g in Heqt.
    simpl fmap in Heqt.
    assert (t =
            (fun (y0 : B0 + (A -> B -> C)) (a : A * B) =>
          Either_bimap (fun p : B0 => (p, a)) (fun f : A -> B -> C => (law3_h f) a) y0)).
    { rewrite Heqt. extensionality y0. extensionality a. destruct y0; destruct a; trivial. }
    rewrite H1. clear H1 Heqt t.
    remember (fun (y0 : B0 + (A -> B -> C)) (a : A * B) =>
           Either_bimap (fun p : B0 => (p, a)) (fun f0 : A -> B -> C => law3_h f0 a) y0) as t.
    remember (fmap[ Select F] law3_f (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y) <*? fmap[ Select F] t z) as p.
    rewrite Select_free_3 in Heqp.
    rewrite fmap_comp_x in Heqp.
    rewrite Heqt in Heqp. clear Heqt t. unfold flip in Heqp.
    remember (fun y : A * B + C =>
            mapLeft
              (fun (y0 : A * B) (x : B0 + (A -> B -> C)) =>
               Either_bimap (fun p : B0 => (p, y0)) (fun f0 : A -> B -> C => law3_h f0 y0) x) 
              (law3_f y)) as t.
    subst p.

    f_equal.
    assert ((fmap[ Select F] func_1 \o fmap[ Select F] (mapLeft reassoc_triple))
      (fmap[ Select F] t (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y) <*? fmap[ Select F] rev_f_ap z) =
            (fmap[ Select F] func_1 (fmap[ Select F] (mapLeft reassoc_triple)
    (fmap[ Select F] t (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y) <*? fmap[ Select F] rev_f_ap z))))
           by reflexivity.
    rewrite H1. clear H1.
    f_equal. clear Heqfunc_1 func_1.

    remember ((fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y)) as p.
    remember (fmap[ Select F] (mapLeft reassoc_triple) (fmap[ Select F] t p <*? fmap[ Select F] rev_f_ap z)) as rhs.
    rewrite Select_free_1 in Heqrhs.
    subst rhs p.

    remember (fmap[ Select F] law3_f x) as x'.
    remember (fmap[ Select F] (fmap[ sum (B0 + (A -> B -> C) -> B0 * (A * B) + C)] (mapLeft reassoc_triple)) ((fmap[ Select F] t (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y)))) as x''.
    remember (x' <*? fmap[ Select F] law3_g (fmap[ Select F] law3_f y <*? fmap[ Select F] law3_g z)) as lhs.
    (* Save 1 *)
    
    
    rewrite Select_free_3 in Heqlhs. subst lhs. subst x'.
    remember (fmap[ Select F] (mapLeft (flip law3_g)) (fmap[ Select F] law3_f x)) as x'.
    remember (x'' <*?
  fmap[ Select F]
    (fun g : (B0 + (A -> B -> C) -> B0 * (A * B) + C) -> B0 * (A * B) + C => mapLeft reassoc_triple \o g)
    (fmap[ Select F] rev_f_ap z)) as rhs.
    rewrite fmap_comp_x in Heqrhs. 
    rewrite Select_free_3 in Heqrhs.
    subst rhs. subst x''.
    remember ( fmap[ Select F] (mapLeft (flip (fun y0 : B0 + (A -> B -> C) => mapLeft reassoc_triple \o rev_f_ap y0)))
    (fmap[ Select F] (fmap[ sum (B0 + (A -> B -> C) -> B0 * (A * B) + C)] (mapLeft reassoc_triple))
       (fmap[ Select F] t (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y)))) as x''.
    remember (fmap[ Select F] law3_f y <*? fmap[ Select F] law3_g z) as z'.
    unfold flip in Heqx''. unfold rev_f_ap in Heqx''. unfold comp in Heqx''.
    rewrite fmap_comp_x in Heqx''.
Admitted.

(* This is a proof of the (Pure Right) case of the distributivity theorem for rigid
   selective functors. Assumes the associativity law. *)
Lemma Select_Selective_law2_case_right `{HF : Functor F} {HFL: FunctorLaws F} :
  forall (A B : Type) (x : B) (y : Select F (A -> B)) (z : Select F (A -> B)),
    select (Pure (Right x)) (y *> z) = (select (Pure (Right x)) y) *> (select (Pure (Right x)) z).
Proof.
  intros A B x y z.
  repeat rewrite sequence_ap.
  simpl "<*>".
  unfold Select_ap.
  repeat rewrite Select_select_to_infix.
  repeat rewrite Select_map_to_fmap.
  repeat rewrite fmap_comp_x.
  remember (  Pure (inr x) <*?
                   (fmap[ Select F] (fun y0 : A -> B => inl (const id y0)) y <*?
                        fmap[ Select F] rev_f_ap z)) as lhs.
  remember (fmap[ Select F] (fun y0 : B => inl (const id y0)) (Pure (inr x) <*? y) <*?
                fmap[ Select F] rev_f_ap (Pure (inr x) <*? z)) as rhs.
  rewrite Select_Selective_law3_assoc in Heqlhs.
  repeat rewrite fmap_comp_x in Heqlhs.
  repeat rewrite Select_free_1 in Heqrhs.
  rewrite Select_Selective_law3_assoc in Heqrhs.
  repeat rewrite fmap_comp_x in Heqrhs.
  remember (fmap[ Select F] (fun y : A + B => law3_g (fmap[ sum A] rev_f_ap y))
             (Pure (inr x))) as p.
  simpl in Heqp.
  rewrite Heqp in Heqrhs. clear Heqp p.
  remember (fmap[ Select F] law3_f
             (fmap[ Select F] (fmap[ sum A] (fun y0 : B => inl (const id y0)))
                (Pure (inr x)) <*?
         fmap[ Select F] (fun g : A -> B => (fun y0 : B => inl (const id y0)) \o g) y)) as p.
  assert (p <*? Pure (law3_g (inr (rev_f_ap x))) =
          either (law3_g (inr (rev_f_ap x))) id <$> p) as H.
  { now rewrite Select_Selective_law1. }
  rewrite H in Heqrhs. clear H.
  rewrite Heqp in Heqrhs. clear Heqp p.
  repeat rewrite fmap_comp_x in Heqrhs.
  rewrite Select_free_1 in Heqrhs.
  repeat rewrite fmap_comp_x in Heqrhs.
  remember (fmap[ Select F]
             (fun y : A + B =>
              fmap[ sum A]
                (fun y0 : (B -> B) + B => either (law3_g (inr (rev_f_ap x))) id (law3_f y0))
                (fmap[ sum A] (fun y0 : B => inl (const id y0)) y)) 
             (Pure (inr x))) as p.
  compute in Heqp. rewrite Heqp in Heqrhs. clear Heqp p.
  remember (fmap[ Select F] law3_f (Pure (inr x))) as p.
  compute in Heqp. rewrite Heqp in Heqlhs. clear Heqp p.
  (* rewrite Select_free_3 in Heqlhs. *)
  remember (fun y : A -> B => law3_g (inl (const id y))) as p_lhs.
  remember (fun y : A -> B => law3_h (rev_f_ap y)) as q_lhs.
  rewrite Select_free_3 in Heqlhs, Heqrhs.
  rewrite Select_free_1 in Heqlhs, Heqrhs.
  rewrite Heqrhs. clear Heqrhs rhs.
  rewrite Heqlhs. clear Heqlhs lhs.
  f_equal.
  rewrite Heqp_lhs. clear Heqp_lhs p_lhs.
  rewrite Heqq_lhs. clear Heqq_lhs q_lhs.
  rewrite fmap_comp_x.
  set (p_lhs := (fmap[ sum A] (mapLeft (flip (fun y0 : A -> B => law3_h (rev_f_ap y0)))))).
  set (q_lhs := (fun y0 : A -> B =>
     mapLeft (flip (fun y1 : A -> B => law3_h (rev_f_ap y1))) \o law3_g (inl (const id y0)))).
  rewrite fmap_comp_x.
  set (p_rhs := (fmap[ sum A] (mapLeft (flip (fun y0 : A -> B => law3_h (rev_f_ap \o y0)))))).
  set (q_rhs := (fun y0 : A -> B =>
     mapLeft (flip (fun y1 : A -> B => law3_h (rev_f_ap \o y1))) \o
     ((fun y1 : (B -> B) + B => either (law3_g (inr (rev_f_ap x))) id (law3_f y1)) \o
      ((fun y1 : B => inl (const id y1)) \o y0)))).
  remember (fmap[ Select F] p_lhs (Pure (inr (inr x))) <*? fmap[ Select F] q_lhs y)
    as lhs.
  remember (fmap[ Select F] p_rhs (Pure (inr (inr x))) <*? fmap[ Select F] q_rhs y)
    as rhs.
  rewrite Select_free_3 in Heqlhs, Heqrhs.
  rewrite fmap_comp_x in Heqlhs, Heqrhs.
  rewrite Heqrhs. clear Heqrhs rhs.
  rewrite Heqlhs. clear Heqlhs lhs.
  f_equal.
  exact HFL.
  exact HFL.
Qed.

(* -- D1 (distributivity): pure x <*? (y *> z) = (pure x <*? y) *> (pure x <*? z) *)
(* d1 :: Selective f => Either a b -> f (a -> b) -> f (a -> b) -> f b *)
(* NB:  This law appers to be a 'theorem' if we only consider rigid selective functos. *)
(* NB2: The following proof assumes 'pure-left' and the associativity law (law 3) *)
Theorem Select_Selective_law2 `{HF : Functor F} {HFL: FunctorLaws F}:
  forall (A B : Type) (x : A + B) (y : Select F (A -> B)) (z : Select F (A -> B)),
    select (pure x) (y *> z) = (select (pure x) y) *> (select (pure x) z).
Proof.
   intros A B x y z.
  destruct x.
  (* x is a Left *)
  - repeat rewrite Select_pure_left.
    repeat rewrite sequence_ap.
    rewrite fmap_comp_x.
    unfold comp.
    unfold const.
    (* rewrite <- ap_fmap. *)
    assert (fmap[ Select F] (fun _ : A -> B => id) y <*> fmap[ Select F] (fun f : A -> B => f a) z =
            fmap[ Select F] (fun _ : A -> B => id) y <*> (pure[ Select F] (fun f : A -> B => f a) <*> z)).
    { now rewrite ap_fmap. }
    unfold rev_f_ap.
    remember (fmap[ Select F] (fun _ : A -> B => id) y <*> fmap[ Select F] (fun f : A -> B => f a) z) as rhs.
    rewrite H in Heqrhs. subst rhs. clear Heqrhs.
    rewrite <- ap_comp.
    assert ((pure[ Select F]) (fun (f : B -> B) (g0 : (A -> B) -> B) (x : A -> B) => f (g0 x)) <*>
             fmap[ Select F] (fun _ : A -> B => id) y <*> (pure[ Select F]) (fun f : A -> B => f a) <*> z =
            ((fmap[ Select F]) (fun (f : B -> B) (g0 : (A -> B) -> B) (x : A -> B) => f (g0 x))
              (fmap[ Select F] (fun _ : A -> B => id) y)) <*> (pure[ Select F]) (fun f : A -> B => f a) <*> z).
    { now rewrite ap_fmap. }
    rewrite H. clear H.
    assert (fmap[ Select F] (fun (f : B -> B) (g0 : (A -> B) -> B) (x : A -> B) => f (g0 x))
                 (fmap[ Select F] (fun _ : A -> B => id) y) =
            fmap[ Select F]
                ((fun (f : B -> B) (g0 : (A -> B) -> B) (x : A -> B) => f (g0 x)) \o (fun _ : A -> B => id))
                y).
    { now rewrite <- fmap_comp. }
    rewrite H. clear H.
    unfold comp.
    rewrite ap_interchange.
    remember (fun f : ((A -> B) -> B) -> (A -> B) -> B => f (fun f0 : A -> B => f0 a)) as p.
    remember (fun (_ : A -> B) (g0 : (A -> B) -> B) (x0 : A -> B) => id (g0 x0)) as q.
    assert ((pure[ Select F]) p <*> fmap[ Select F] q y <*> z =
            (fmap[ Select F]) p (fmap[ Select F] q y) <*> z).
    { now rewrite ap_fmap. }
    rewrite H. clear H.
    assert (fmap[ Select F] p (fmap[ Select F] q y) <*> z =
            fmap[ Select F] (p \o q) y <*> z).
    { now rewrite <- fmap_comp. }
    rewrite H. clear H.
    rewrite Heqp. rewrite Heqq. clear Heqp p Heqq q.
    unfold comp.
    unfold id.
    assert (fmap[ Select F] (fun f : A -> B => f a) (fmap[ Select F] (fun _ x : A -> B => x) y <*> z) =
            pure[ Select F] (fun f : A -> B => f a) <*> (fmap[ Select F] (fun _ x : A -> B => x) y <*> z)).
    { now rewrite ap_fmap. }
    remember (fmap[ Select F] (fun f : A -> B => f a) (fmap[ Select F] (fun _ x : A -> B => x) y <*> z)) as lhs.
    rewrite H in Heqlhs. subst lhs. clear Heqlhs.
    rewrite <- ap_comp.
    remember (fun (f : (A -> B) -> B) (g0 : (A -> B) -> A -> B) (x : A -> B) => f (g0 x)) as p.
    remember (fun f : A -> B => f a) as q.
    remember (fun _ x : A -> B => x) as r.
    assert ((pure[ Select F]) p <*> (pure[ Select F]) q <*> fmap[ Select F] r y <*> z =
            ((pure[ Select F]) (p q)) <*> fmap[ Select F] r y <*> z).
    { now rewrite ap_homo. }
    rewrite H. clear H.
    assert ((pure[ Select F]) (p q) <*> fmap[ Select F] r y <*> z =
            (fmap[ Select F]) (p q) (fmap[ Select F] r y) <*> z).
    { now rewrite ap_fmap. }
    rewrite H. clear H.
    assert (fmap[ Select F] (p q) (fmap[ Select F] r y) <*> z =
            fmap[ Select F] ((p q) \o r) y <*> z).
    { now rewrite <- fmap_comp. }
    rewrite H. clear H.
    rewrite Heqp. rewrite Heqq. rewrite Heqr. clear Heqp r Heqq q Heqr r.
    reflexivity.
  (* x is a Right *)
  - apply Select_Selective_law2_case_right.
Qed.
