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
  | MkSelect : forall B C, (C -> ((B -> A) + A)) -> Select F C -> F B -> Select F A.

Arguments Pure {F} {A}.
Arguments MkSelect {F} {A} {B} {C}.

(******************************************************************************)
(************************ Functor and FunctorLaws *****************************)
(******************************************************************************)
(* Note that `fmap` for `Select` implementation uses two `Functor` instances in its
   implemetation:
     Either for the first argument of the `MkSelect` constructor and
     Function for the second.
   Here we avoid using the instances and instead use the appropriate `fmap`
   implementations explicitely: `Either_map` and function composition
*)
Equations Select_map {A B : Type} `{Functor F}
           (f : A -> B) (x : Select F A) : Select F B :=
Select_map f (Pure a) => Pure (f a);
Select_map f (MkSelect g x y) =>
  MkSelect (fun x => Either_bimap (fun k => f \o k) f (g x))
           x
           y.
           (* ((fun k : _ -> A => f \o k) <$> y). *)

Program Instance Select_Functor (F : Type -> Type)
  `{Functor F} : Functor (Select F) := {
  fmap := fun _ _ f x => Select_map f x
}.

(* Auxiliary lemmas for proving Functor laws *)
Definition id_f {A : Type} (x : A) := x.

Lemma id_x_is_x {A : Type}:
  forall (x : A), id x = x.
Proof. intros x. reflexivity. Qed.


Lemma compose_id {A B : Type}:
  forall (f : A -> B), (compose f id) = f.
Proof.
  intros f.
  extensionality x.
  unfold compose.
  now rewrite id_x_is_x.
Qed.

Lemma id_comp {A B : Type}:
  forall (f : A -> B), (id \o f) = f.
Proof.
  intros f.
  extensionality x.
  now unfold comp.
Qed.

Lemma Either_map_id {E X : Type} : Either_map (E:=E) (@id X) = id.
Proof.
  extensionality x.
  now destruct x.
Qed.

Lemma Either_map_comp {E A B C : Type} :
  forall (f : B -> C) (g : A -> B),
  Either_map (E:= E) f \o Either_map g = Either_map (f \o g).
Proof.
  intros f g.
  extensionality x.
  now destruct x.
Qed.

Import FunctorLaws.

Lemma fmap_rewrite_compose {A B C : Type} `{Functor F} :
  forall (f : B -> C) (g : A -> B) (x : F A),
    fmap f (fmap g x) = (fmap f \o fmap g) x.
Proof.
  intros f g x.
  reflexivity.
Qed.

Program Instance Select_FunctorLaws `{FunctorLaws F} : FunctorLaws (Select F).
(* Theorem Select_Functor_law1 {A : Type} *)
(*         `{Functor F} `{FunctorLaws F} : *)
(*   forall (x : Select F A), fmap id x = id x. *)
Obligation 1.
unfold id.
extensionality x.
induction x.
- rewrite Select_map_equation_1. reflexivity.
- rewrite Select_map_equation_2.
  f_equal.
  remember (fun k : B -> A => (fun x1 : A => x1) \o k)  as t.
  assert ((fun x1 : A => x1) = id).
  { reflexivity. }
  rewrite H1 in *.
  rewrite Heqt.
  extensionality y.
  unfold Either_bimap.
  destruct (s y).
  + now rewrite id_comp.
  + now rewrite id_x_is_x.
Qed.
(* Theorem Select_Functor_law2 {A B C : Type} *)
(*         `{Functor F} `{FunctorLaws F} : *)
(*   forall (f : B -> C) (g : A -> B) (x : Select F A), *)
(*   ((Select_map f) \o (Select_map g)) x = Select_map (f \o g) x. *)
Obligation 2.
extensionality x.
simpl.
(* It is SUPER IMPORTANT to generalise the two type variables B and C *)
(*    (and thus also the functions f and g), because otherwise the *)
(*    inductive hypothesis will be not general enough! *)
revert b c g f.
induction x.
- simpl in *. trivial.
- intros b c g f0.
  repeat rewrite Select_map_equation_2.
  f_equal.
  + extensionality x0.
    unfold Either_bimap.
    destruct (s x0); reflexivity.
Qed.

(* (******************************************************************************) *)
(* (************************ Selective               *****************************) *)
(* (******************************************************************************) *)

(* -- TODO: Prove that this is a lawful 'Selective'. *)
(* instance Functor f => Selective (Select f) where *)
(*     -- Identity law *)
(*     select f x (Pure y) = either ($y) id . f <$> x *)

(*     -- Associativity law *)
(*     select f x (Select g y z) = Select id (select h x y) z *)
(*       where *)
(*         h a = case f a of Right r -> Right (Right r) *)
(*                           Left dr -> Left  (bimap (dr.) dr . g) *)


Definition h {A B C D E F: Type}
           (f : A -> ((B -> C) + C))
           (g : D -> ((E -> B) + B))
           (a : A) : Either (D -> Either (E -> C) C) (Either F C) :=
  match f a with
  | inr r  => Right (Right r)
  | inl dr => Left  (Either_bimap (fun k => dr \o k) dr \o g) 
  end.

Equations Select_select {A B C : Type} `{Functor F}
          (f : A -> ((B -> C) + C))
          (x : Select F A)
          (a : Select F B) : Select F C
          :=
Select_select f x (Pure y) := (either (fun k => k y) id \o f) <$> x;
Select_select f x (MkSelect g y z) :=
  MkSelect id (Select_select (h f g) x y) z.

(* apS :: Selective f => f (a -> b) -> f a -> f b *)
(* apS = select Left *)

Definition Select_ap {A B : Type} `{Functor F}
           (f : Select F (A -> B)) (x : Select F A) : Select F B :=
  Select_select Left f x.

Program Instance Select_Applicative
        (F : Type -> Type) `{Functor F} : Applicative (Select F) :=
  { is_functor := Select_Functor F
  ; pure _ x := Pure x
  ; ap _ _ f x := Select_ap f x
}.

Import ApplicativeLaws.
Set Printing Universes.

Program Instance Select_ApplicativeLaws `{FunctorLaws F} : ApplicativeLaws (Select F).
Obligation 1.
Proof.
  extensionality x.
  rewrite id_x_is_x.
  unfold Select_ap.
  generalize dependent a.
  generalize dependent H.
  generalize dependent F.
  induction x.
  destruct x.
  - reflexivity.
  - rewrite Select_select_equation_2.
    remember ((Select_select (h inl s) (Pure id) x)) as t.
Admitted.
Obligation 2.
  simpl.
(* Program Instance Select_Applicative *)
(*         (F : Type -> Type) `{Functor F} : Applicative (Select F) := *)
(*   { is_functor := Select_Functor F *)
(*   ; pure _ x := Pure x *)
(*   ; ap _ _ f x := Select_ap f x *)
(* }. *)

(* (******************************************************************************) *)
(* (***************** Aux theorems ***********************************************) *)
(* (******************************************************************************) *)
(* (* -- P1 (Generalised identity): select x (pure y) == either y id <$> x *) *)
(* (* p1 :: Selective f => f (Either a b) -> (a -> b) -> f b *) *)
(* (* p1 x y = select x (pure y) === either y id <$> x *) *)
(* Theorem P1 {A B : Type} `{FunctorLaws F} : *)
(*   forall (x : Select F (Either A B)) (y : A -> B), *)
(*     Select_select x (pure y) = either y id <$> x. *)
(* Proof. *)
(*   intros x y. simpl. *)
(*   now rewrite Select_select_equation_1. *)
(* Qed. *)

(* Theorem P2 {A B : Type} `{FunctorLaws F} : *)
(*   forall (x : A) (y : Select F (A -> B)),   *)
(*   Select_select (Pure (inl x)) y = y <*> pure x. *)
(*   (* Select_select (Pure (inl x)) y = y <*> Pure x. *) *)
(* Proof. *)
(*   revert A B. *)
(*   destruct y. *)
(*   - reflexivity. *)
(*   - (* rewrite Select_select_equation_2. *) *)
(*     simpl "<*>". unfold Select_ap. *)
(*     remember  (fmap[ Select F] (fun (y0 : A) (g : A -> B) => g y0) (Pure x)) as t. *)
(*     simpl in Heqt. *)
(*     rewrite Select_map_equation_1 in Heqt. *)
(*     rewrite Heqt. clear Heqt. clear t. *)

(*     rewrite Select_select_equation_1. *)
(*     remember (fmap[ Select F] (either (fun g : A -> B => g x) id) (fmap[ Select F] inl (MkSelect y f))) as rhs. *)
(*     assert (Htemp : rhs = fmap ((either (fun g : A -> B => g x) id) \o inl) (MkSelect y f)). *)
(*     { rewrite Heqrhs. now rewrite <- fmap_comp. } *)
(*     rewrite Heqrhs. rewrite Heqrhs in Htemp. rewrite Htemp. *)
(*     clear Htemp. clear Heqrhs. clear rhs. *)
(*     remember (either (fun g : A -> B => g x) id \o inl) as temp. *)
(*     simpl fmap. *)
(*     rewrite Select_map_equation_2. *)
(*     rewrite Select_select_equation_2. *)
(*     unfold law3_h. *)
(*     remember (fmap[ F] (fun f0 : b -> A -> B => uncurry f0) f) as lhs_q. *)
(*     remember (fmap[ F] (fun k : b -> A -> B => temp \o k) f) as rhs_q. *)


(*     repeat rewrite Select_map_equation_1. *)
(*     rewrite Select_select_equation_1. *)
(*     simpl. *)
(*     remember (fun g : A -> B => g x) as rhs_p. *)
(*     remember (MkSelect (Select_map (Either_map inl) y) (fmap[ F] (fun k : b -> A -> B => inl \o k) f)) as rhs_q. *)
(*     pose (Htemp := @P1 (A -> B) B F H H0). simpl in Htemp. *)
(*     rewrite <- (Htemp rhs_q rhs_p). clear Htemp. *)
(*     simpl. *)

(*     unfold law3_f in Heqt. simpl in Heqt. rewrite Heqt. clear Heqt. clear t. *)
(*     remember (Select_select (Pure (inl x)) (Select_map law3_g y)) as lhs_p. *)
(*     remember (Select_map (Either_map (fun k : A -> B => k x)) y) as  rhs_p. *)
(*     remember (fmap[ F] law3_h f) as lhs_q. *)
(*     remember (fmap[ F] (fun k : b -> A -> B => (fun k0 : A -> B => k0 x) \o k) f) as rhs_q. *)

(*     unfold "\o" in Heqrhs_q. *)

(* Theorem P2 {A B : Type} `{FunctorLaws F} : *)
(*   forall (x : A) (y : Select F (A -> B)),   *)
(*   Select_select (Pure (inl x)) y = Select_map (fun k => k x) y. *)
(*   (* Select_select (Pure (inl x)) y = y <*> Pure x. *) *)
(* Proof. *)
(*   Set Printing Universes. *)
(*   Check A. *)
(*   Check (A -> B). *)
(*   revert A B. *)

(*   Check Select_ind. *)
(*   induction y as [| C b s IH handler]. *)

(*   destruct y. *)
(*   - reflexivity. *)
(*   - rewrite Select_select_equation_2. simpl. *)
(*     rewrite Select_map_equation_2. *)
(*     rewrite Select_map_equation_1. *)
(*     remember (law3_f (inl x)) as t. *)
(*     unfold law3_f in Heqt. simpl in Heqt. rewrite Heqt. clear Heqt. clear t. *)
(*     remember (Select_select (Pure (inl x)) (Select_map law3_g y)) as lhs_p. *)
(*     remember (Select_map (Either_map (fun k : A -> B => k x)) y) as  rhs_p. *)
(*     remember (fmap[ F] law3_h f) as lhs_q. *)
(*     remember (fmap[ F] (fun k : b -> A -> B => (fun k0 : A -> B => k0 x) \o k) f) as rhs_q. *)

(*     unfold "\o" in Heqrhs_q. *)

(*   Check Select_ind. *)
(*   (* induction y as [| C b s IH handler]. *) *)
(*   (* destruct y. *) *)
(*   (* - reflexivity. *) *)
(*   (* - rewrite Select_select_equation_2. *) *)
(*   (*   rewrite Select_map_equation_2. *) *)
(*   (*   f_equal. *) *)
(*   (* rewrite Select_select_unfold_eq. *) *)
(*   (* Search Select_select. *) *)
(*   (* unfold Select_select_unfold. *) *)
(* Admitted. *)

(* Import ApplicativeLaws. *)

(* Program Instance Select_ApplicativeLaws `{FunctorLaws F} : ApplicativeLaws (Select F). *)
(* (* (forall (F : Type -> Type) (H : Functor F), *) *)
(* (*  FunctorLaws F -> forall a : Type, ap[ Select F] ((pure[ Select F]) id) = id). *) *)
(* (* pure id <*> v = v   *) *)
(* Obligation 1. *)
(* (* extensionality x. *) *)
(* (* revert a x. *) *)
(* (* induction x as [| A b s IH handler]; simpl in *; trivial. *) *)
(* (* - unfold id at 2. unfold id at 2 in IH. *) *)
(* (*   unfold Select_ap. *) *)
(* (*   simpl fmap at 2. *) *)
(* (*   rewrite Select_map_equation_2 at 1. *) *)
(* (*   rewrite Select_select_equation_2 at 1. *) *)
(* (*   unfold id. *) *)
(* (*   remember ( *) *)
(* (*     (Select_select (fmap[ Select F] law3_f (fmap[ Select F] inl (Pure (fun x : A => x)))) *) *)
(* (*        (fmap[ Select F] law3_g (Select_map (Either_map (fun (y : A) (g : A -> A) => g y)) s))) *) *)
(* (*        ) as lhs1. *) *)
(* (*   remember ( *) *)
(* (*           (fmap[ F] law3_h (fmap[ F] (fun k : b -> A => (fun (y : A) (g : A -> A) => g y) \o k) handler)) *) *)
(* (*        ) as lhs2. *) *)

(* (* unfold Select_ap. simpl. revert a x. *) *)
(* (* induction x as [| A b s IH handler]. *) *)
(* (* - simpl. *) *)
(* (*   repeat rewrite Select_map_equation_1. *) *)
(* (*   repeat rewrite Select_select_equation_1. simpl fmap. *) *)
(* (*   repeat rewrite Select_map_equation_1. reflexivity. *) *)
(* (* - repeat rewrite Select_map_equation_1 in *. *) *)
(* (*   repeat rewrite Select_map_equation_2 in *. *) *)
(* (*   rewrite Select_select_equation_2. simpl. *) *)
(* (*   repeat rewrite Select_map_equation_1. *) *)
(* (*   unfold id at 2. *) *)
(* (*   unfold law3_f, law3_h. simpl. *) *)
(* (*   remember ((Either_map (E:=b) (fun (y : A) (f : A -> A) => f y))) as func1. *) *)
(* (*   rewrite Select_Functor_law2. *) *)
  

(* (*   rewrite IH. *) *)
(* (*   Check Select_select_equation_2. *) *)
(* (*   rewrite Select_select_equation_2. simpl. *) *)
(* (*   unfold id. *) *)
(* (*   simpl in * |- *. *) *)
(* (*   pose (term1 := *) *)
(* (*    (Select_select (Pure (law3_f (inl id))) *) *)
(* (*                   (Select_map law3_g (Select_map (Either_map (fun (y : A) (f : A -> A) => f y)) s)))). *) *)
(* (*   pose (term2 := *) *)
(* (*     (fmap[ F] law3_h (fmap[ F] (fun k : b -> A => (fun (y : A) (f : A -> A) => f y) \o k) handler))). *) *)
(* (*   assert (H : (Select_map (fun (y : b + A) (f : b + A -> b + A) => f y) s) = s). *) *)
(* (*   assert (H : (Select_select (Pure (law3_f (inl id))) *) *)
(* (*                              (Select_map law3_g (Select_map (Either_map (fun (y : A) (f : A -> A) => f y)) s))) *) *)
(* (*               = s). *) *)
(* (*   { *) *)


(* (* induction x as [| A b s IH handler]; simpl in *; trivial. *) *)
(* (* - unfold Select_ap, id in *. *) *)
(* Admitted. *)
(* Obligation 2. *)
(* (* pure (.) <*> u <*> v <*> w = u <*> (v <*> w) *) *)
(* revert a b c v u w. *)
(* intros A B C v u w.   *)
(* (* pure (.) <*> u <*> v <*> w = u <*> (v <*> w) *) *)
(* Admitted. *)
(* Obligation 4. *)
(* (* u <*> pure y = pure ($ y) <*> u   *) *)
(* Admitted. *)
(* Obligation 5. *)
(* Admitted. *)

(* Program Instance Select_Selective (F : Type -> Type) `{Functor F}: Selective (Select F) := *)
(*   { is_applicative := Select_Applicative F *)
(*     ; select _ _ x f := Select_select x f *)
(*   }. *)

(* (******************** Selective laws *****************************) *)
(* Theorem select_selective_law1_identity *)
(*   {A : Type} {F : Type -> Type} `{Functor F} {x : Select F (Either A A)} : *)
(*   x <*? (pure id) = either id id <$> x. *)
(* Proof. *)
(*     destruct x. *)
(*   - simpl. *)
(*     reflexivity. *)
(*   - destruct x; *)
(*     simpl; *)
(*     reflexivity. *)
(* Qed. *)

(* Theorem select_selective_law2_distr *)
(*   {A B : Type} {F : Type -> Type} `{Functor F} *)
(*   (x : (Either A B)) *)
(*   (y : Select F (A -> B)) *)
(*   (z : Select F (A -> B)) : *)
(*   pure x <*? (y *> z) = (pure x <*? y) *> (pure x <*? z). *)
(* Proof. *)
(* Admitted.         *)

(* Theorem select_selective_law3_assoc *)
(*   {A B C : Type} {F : Type -> Type} `{Functor F} *)
(*   (x : Select F (B + C)) *)
(*   (y : Select F (A + (B -> C))) *)
(*   (z : Select F (A -> B -> C)) : *)
(*   x <*? (y <*? z) = (law3_f <$> x) <*? (law3_g <$> y) <*? (law3_h <$> z). *)
(* Proof. *)
(*   simpl. *)
(*   revert A y z. *)
(*   induction x. *)
(*   (* destruct y. *) *)
(*   (* - simpl. *) *)
(*   (*   destruct x. *) *)
(*   (*   + simpl. *) *)

(*   (* - destruct y. *) *)
(*   (*   + destruct s; *) *)
(*   (*     simpl; reflexivity. *) *)
(*   (*   + destruct s; *) *)
(*   (*     destruct z; *) *)
(*   (*     destruct s0; *) *)
(*   (*     simpl; reflexivity. *) *)
(* Admitted. *)

