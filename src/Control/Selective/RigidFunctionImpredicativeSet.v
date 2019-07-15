Require Import Coq.Program.Basics.
Require Import Hask.Prelude.
Require Import Data.Functor.
Require Import Data.Either.
Require Import Control.Applicative.
(* Require Import Control.Selective. *)
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

Definition void := Empty_set.

Inductive Select (F : Type -> Type) (A : Set) : Set :=
    Pure   : A -> Select F A
  | MkSelect : forall (B : Set), Select F (B + A) -> F (B -> A) -> Select F A.

Check Select_ind.

(* Inductive Select (F : Type -> Type) : Set -> Set := *)
(*     Pure   : forall (A : Set), A -> Select F A *)
(*   | MkSelect : forall (A B : Set), Select F (B + A) -> F (B -> A) -> Select F A. *)

Arguments Pure {F} {A}.
Arguments MkSelect {F} {A} {B}.

Function Select_map {A B : Set} `{Functor F}
         (f : A -> B) (x : Select F A) : Select F B :=
  match x with
  | Pure a => Pure (f a)
  | MkSelect x y => MkSelect (Select_map (Either_map f) x)
                             (fmap (fun k : _ -> A => f \o k) y)
  end.

Functional Scheme Select_map_ind := Induction for Select_map Sort Prop.

Check Select_ind.

(* Lemma t : forall (A : Type), (void + A)%type = A. *)
(* Proof. *)
(*   intros A. *)

Definition void_id  : forall (A : Set), (void + A)%type = A.
Admitted.

Definition Select_add_void {A : Set} `(x : Select F A) : Select F (void + A).
Proof.
  destruct x.
  - rewrite void_id. exact (Pure a).
  - pose (t := MkSelect x f).
    rewrite <- void_id in t.
    exact t.
Defined.

Definition Select_drop_void {A : Set} `(x : Select F (void + A)) : Select F A.
Proof.
  destruct x.
  - rewrite <- void_id. exact (Pure s).
  - pose (t := MkSelect x f).
    rewrite void_id in t.
    exact t.
Defined.

Local Coercion Select_add_void : Sortclass >-> Funclass.
Local Coercion Select_drop_void : Sortclass >-> Funclass.

Check (Select_add_void (Pure O)). 
Set Printing Coercions.
Check (Select_add_void (Pure O)). 
Check (Select_drop_void (Select_add_void (Pure O))). 

(* Definition Select_ind' *)
(*      : forall (F : Type -> Type) (A B : Set) (P : forall {X : Set}, Select F (X + (A -> B)) -> Prop), *)
(*        (forall (a : (A -> B)), P (Select_add_void (Pure a))) -> *)
(*        (forall (X : Set) (s : Select F (X + (A -> B))), *)
(*            P s -> forall f0 : F (X -> (A -> B)), P (Select_add_void (MkSelect s f0))) -> *)
(*        forall (s : Select F (A -> B)), P (Select_add_void s). *)
(* Proof. *)
(* Admitted. *)

Check Select_ind.
(* Definition Select_ind'' *)
(*      : forall (F : Type -> Type) (X : Set) (P : forall (A : Set) (HA : A = X), Select F A -> Prop), *)
(*        (forall (a : X), P X eq_refl (Pure a)) -> *)
(*        (forall (B : Set) (s : Select F (B + X)), *)
(*            P (B + X)%type _ s -> forall f0 : F (B -> X), P X eq_refl (MkSelect s f0)) -> *)
(*        forall (s : Select F X), P X eq_refl s. *)

Definition Select_ind'
     : forall (F : Type -> Type) (A B : Set) (P : forall (X : Set), Select F (X + (A -> B)) -> Prop),
       (forall (a : (A -> B)), P void (Select_add_void (Pure a))) ->
       (forall (X : Set) (s : Select F (X + (A -> B))),
           P X s -> forall f0 : F (X -> (A -> B)), P void (Select_add_void (MkSelect s f0))) ->
       forall (s : Select F (A -> B)), P void (Select_add_void s).
Proof.
Admitted.

Require Import Coq.Program.Equality.

(* Lemma Select_induction_fail `{Functor F} : *)
(*   (* forall (A B : Set) (a : A) (x : Select F (void + (A -> B))), *) *)
(*   (*   Select_map (Either_map (fun f => f a)) x = Select_map (Either_map (fun f => f a)) x. *) *)
(*   forall (A B : Set) (a : A) (x : Select F ((A -> B))), *)
(*     Select_map ((fun f => f a)) x = Select_map ((fun f => f a)) x. *)
(* Proof. *)

(*   intros A B a x. *)

(*   dependent induction x. *)
(*   - admit. *)
(*   -  *)

(*   refine (@Select_ind' F A B *)
(*     (* (fun X (y : Select F (X + (A -> B))) => Select_map (Either_map (fun f  : A -> B => f a)) y = *) *)
(*     (*             Select_map (Either_map (fun f => f a)) y) _ _  (x)). *) *)
(*       (fun X (y : Select F (X + (A -> B))) => Select_map (Either_map (fun f  : A -> B => f a)) y = *)
(*                                               Select_map (Either_map (fun f => f a)) y) *)
(*            _ _  (Select_drop_void x)). *)
(*   induction x using Select_ind'. *)
(*   intros A B a x. *)
(*   refine (Select_ind F *)
(*     (fun _ x => Select_map (rev_f_ap a) x = Select_map (rev_f_ap a) x)). *)
(*   induction x with Select_ind'. *)
(*   induction x. *)

(* Require Import Coq.Lists.List. *)
(* Open Scope list_scope. *)


(* Check list_ind. *)

(* Definition list_ind *)
(*      : forall (A : Type) (P : list A -> Prop), *)
(*        P nil -> (forall (a : A) (l : list A), P l -> P (a :: l)) -> forall l : list A, P l. *)


(* Definition list_ind *)
(*      : forall (P : forall A, list A -> Prop), *)
(*     (forall A, P A nil) -> (forall A (a : A) (l : list A), P A l -> P A (a :: l)) -> *)
(*     (forall A, forall l : list A, P A l). *)
(* Admitted. *)

(* Check Select_ind. *)

(* Definition list_ind' : forall (P : forall (A : Type), list A -> Prop), *)
(*     (forall (A : Type), P A nil) -> *)
(*     (forall (A : Type) (a : A) (l : list A), P A l -> P A (a :: l)) -> *)
(*     (forall (A : Type) (l : list A), P A l). *)
(* Proof. *)
(*   intros. *)
(*   induction l. *)
(*   - apply H. *)
(*   - apply H0. apply IHl. *)
(* Qed. *)

(* Lemma t `{Functor F} : *)
(*   forall (A B : Set) (a : A) (x : list (A -> B)), *)
(*     map (rev_f_ap a) x = map (rev_f_ap a) x. *)
(* Proof. *)
(*   Check list_ind. *)
(*   intros A B a x. *)
(*   induction x with list_ind'. *)

(* (* Definition Select_ind' *) *)
(* (*      : forall (A : Set) (F : Type -> Type) (P : forall A : Set, Select F A -> Prop), *) *)
(* (*        (forall (a : A), P A (Pure a)) -> *) *)
(* (*        (forall (B : Set) (s : Select F (B + A)), P (B + A)%type s -> forall f0 : F (B -> A), P A (MkSelect s f0)) -> *) *)
(* (*        forall (s : Select F A), P A s. *) *)
(* (* Admitted. *) *)

Inductive Select' (F : Type -> Type) (A : Set) : Type :=
    Pure'     : forall (B : Set), (B + A) -> Select' F A
  | MkSelect' : forall (B : Set), Select' F (B + A) -> F (B -> A) -> Select' F A.

Check Select'_rect.

(* Inductive Select' (F : Type -> Type) (A : Type) : Type := *)
(*     Pure'   : A -> Select' F A *)
(*   | MkSelect' : forall (B : Type), Select' F (B + A) -> F (B -> A) -> Select' F A. *)

(* (* Inductive Select (F : Type -> Type) : Set -> Set := *) *)
(* (*     Pure   : forall (A : Set), A -> Select F A *) *)
(* (*   | MkSelect : forall (A B : Set), Select F (B + A) -> F (B -> A) -> Select F A. *) *)

(* Arguments Pure' {F} {A}. *)
(* Arguments MkSelect' {F} {A} {B}. *)

(* Function Select_map' {A B : Type} `{Functor F} *)
(*          (f : A -> B) (x : Select' F A) : Select' F B := *)
(*   match x with *)
(*   | Pure' a => Pure' (f a) *)
(*   | MkSelect' x y => MkSelect' (Select_map' (Either_map f) x) *)
(*                                (fmap (fun k : _ -> A => f \o k) y) *)
(*   end. *)

(* Definition Select_ind' *)
(*      : forall (A : Set) (F : Type -> Type) (P : forall (B : Set), Select F (B + A) -> Prop), *)
(*        (forall (a : A), P void (Select_coerce (Pure a))) -> *)
(*        (forall (B : Set) (s : Select F (B + A)), P B s -> *)
(*           forall f0 : F (B -> A), P void (Select_coerce (MkSelect s f0))) -> *)
(*        forall (s : Select F A), P void (Select_coerce s). *)
(* Admitted. *)

(* Lemma Select_induction_fail `{Functor F} : *)
(*   forall (A B : Set) (a : A) (x : Select F (A -> B)), *)
(*     Select_map (fun f => f a) x = Select_map (fun f => f a) x. *)
(* Proof. *)
(*   induction x. *)
(*   intros A B a x. *)
(*   refine (Select_ind F *)
(*     (fun _ x => Select_map (rev_f_ap a) x = Select_map (rev_f_ap a) x)). *)
(*   induction x with Select_ind'. *)
(*   induction x. *)

(* Lemma t `{Functor F} : *)
(*   forall (A B : Set) (a : A) (x : Select F (A -> B)), *)
(*     Select_map (rev_f_ap a) x = Select_map (rev_f_ap a) x. *)
(* Proof. *)
(*   intros A B a x. *)
(*   induction x. *)
(*   induction x with Select_ind'. *)
(*   refine (Select_ind' (A -> B) F *)
(*     (fun _ x => Select_map (rev_f_ap a) x = Select_map (rev_f_ap a) x)). *)
(*   induction x with Select_ind'. *)
(* Admitted. *)
  (* induction x. *)
  (* functional induction (Select_map (rev_f_ap a) x). *)
  (*   refine (Select_ind' (A -> B) F *)
  (*   (fun P (x : Select F P) => Select_map (rev_f_ap a) x = Select_map (rev_f_ap a) x) *)
  (*        _ _ _ _). *)
  (* induction x using Select_ind'. *)

(* Lemma t' `{Functor F} : *)
(*   forall (A B : Type) (a : A) (x : Select' F (A -> B)), *)
(*     Select_map' ((fun (a : A) (f : A -> B) => f a) a) x = Select_map' ((fun (a : A) (f : A -> B) => f a) a) x. *)
(* Proof. *)
(*   intros A B a x. *)
(*   induction x. *)
(*   functional induction (Select_map (rev_f_ap a) x). *)
(*     refine (Select_ind' (A -> B) F *)
(*     (fun P (x : Select F P) => Select_map (rev_f_ap a) x = Select_map (rev_f_ap a) x) *)
(*          _ _ _ _). *)
(*   induction x using Select_ind'. *)

Lemma Select_map_equation_1 :
  forall (A B : Set) `(Functor F)
  (f : A -> B) (a : A),
    Select_map f (Pure a) = Pure (f a).
Proof. trivial. Qed.

Lemma Select_map_equation_2 :
  forall (A B X : Set) `(Functor F)
  (f : A -> B) (x : Select F (X + A)) (y : F (X -> A)),
    Select_map f (MkSelect x y) = MkSelect (Select_map (Either_map f) x)
                                           (fmap (fun k : _ -> A => f \o k) y).
Proof. trivial. Qed.

(* Program Instance Select_Functor `{Functor F} : Functor (Select F) := { *)
(*   fmap := fun _ _ f x => Select_map f x *)
(* }. *)

Import FunctorLaws.

Theorem Select_Functor_law1 {A : Set}
        `{Functor F} `{FunctorLaws F} :
  forall (x : Select F A), Select_map id x = id x.
Proof.
  unfold id.
  intros x.
  generalize dependent x.
  generalize dependent A.
  induction x; trivial.
  rewrite Select_map_equation_2.
  assert (forall A, (fun x0 : A => x0) = id) as H_subst_id.
  { reflexivity. }
  f_equal.
  - rewrite H_subst_id in *. rewrite Either_map_id. now rewrite IHx.
  - rewrite H_subst_id in *. now rewrite fmap_id.
Qed.

Theorem Select_Functor_law2 {A B C : Set}
        `{Functor F} `{FunctorLaws F} :
  forall (f : B -> C) (g : A -> B) (x : Select F A),
    ((Select_map f) \o (Select_map g)) x = Select_map (f \o g) x.
Proof.
Admitted.

Theorem Select_map_comp_x {A B C : Set}
        `{Functor F} `{FunctorLaws F} :
  forall (f : B -> C) (g : A -> B) (x : Select F A),
    Select_map f (Select_map g x) = Select_map (f \o g) x.
Proof.
Admitted.

Fixpoint Select_depth {A : Set} {F : Type -> Type}
         (x : Select F A) : nat :=
  match x with
  | Pure a => O
  | MkSelect y _ => S (Select_depth y)
  end.

Lemma Select_fmap_preserves_depth {A B : Set} `{Functor F} :
  forall (x : Select F A) (f : A -> B),
  Select_depth (Select_map f x) = Select_depth x.
Proof.
  intros x.
  revert B.
  induction x as [| A b s IH handler]; trivial; simpl in *; intros f1 B.
  - simpl Select_map. simpl Select_depth. now rewrite IH.
Qed.

Definition law3_f {A B C : Set}
           (x : B + C) : B + (A + C) := Either_map Right x.

Definition law3_g {A B C : Set}
           (y : A + (B -> C)) : B -> A * B + C :=
  fun a => Either_bimap (fun p => pair p a) (rev_f_ap a) y.

Definition law3_h  {A B C : Set}
           (f : A -> B -> C) : A * B -> C := uncurry f.

Definition Select_depth_order {A : Set} {F : Type -> Type}
           (x : Select F A) (y : Select F A) :=
  Select_depth x < Select_depth y.

Hint Constructors Acc.

Definition Select_erase_type {A : Set} `{Functor F} (x : Select F A) :
  Select F unit :=
  Select_map (const tt) x.

Function Select_select_help {A B : Set} `{H : Functor F}
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

Definition Select_select  {A B : Set} `{H : Functor F}
           (x : Select F (A + B)) (handler : Select F (A -> B)) :
  Select F B :=
  Select_select_help A B F H x handler (Select_erase_type handler) eq_refl.

Lemma Select_select_equation_1 : forall (A B : Set) `(H : Functor F)
         (x : Select F (A + B)) (y : A -> B),
    Select_select x (Pure y) = Select_map (either y id) x.
Proof.
  intros A B F H x y.
  unfold Select_select.
  now rewrite Select_select_help_equation.
Qed.

Lemma Select_select_equation_2 : forall (A B C : Set) `(H : Functor F)
         (x : Select F (A + B)) (y : Select F (C + (A -> B))) (z : F (C -> A -> B)),
    Select_select x (MkSelect y z) =
     MkSelect (Select_select (Select_map law3_f x) (Select_map law3_g y)) (law3_h <$> z).
Proof.
  intros A B C F H x y z.
  unfold Select_select.
  now rewrite Select_select_help_equation.
Qed.

Definition Select_ap {A B : Set} `{Functor F}
           (f : Select F (A -> B)) (x : Select F A) : Select F B :=
  Select_select (Select_map Left f) (Select_map rev_f_ap x).

Lemma Select_depth_pure `{FunctorLaws F}:
  forall (A : Set) (x : Select F A),
    Select_depth x = 0 -> exists a, x = Pure a.
Proof.
   destruct x; simpl.
   - now exists a.
   - discriminate.
Qed.

Lemma Select_depth_mkSelect `{FunctorLaws F} :
  forall (A : Set) (p : Select F A),
    Select_depth p > 0 -> exists B y z, p = MkSelect (B:=B) y z.
Proof.
  intros X p Hp.
  destruct p.
  - simpl in Hp. unfold ">" in Hp. inversion Hp.
  - exists B. exists p. exists f. reflexivity.
Qed.

Theorem Select_Functor_law1_by_depth_ind {A : Set}
        `{Functor F} `{FunctorLaws F} :
  forall (x : Select F A), Select_map id x = id x.
Proof.
  unfold id.
  intros x.
  remember (Select_depth x) as n.
  generalize dependent A.
  revert n.
  induction n.
  - intros.
    symmetry in Heqn.
    destruct (Select_depth_pure _ _ Heqn).
    rewrite H2. now simpl.
  - intros.

     assert (H_d_mkSelect : Select_depth x = S n -> Select_depth x > 0).
     { omega. }
     symmetry in Heqn.
     specialize (H_d_mkSelect Heqn).
     pose (H_d := Select_depth_mkSelect A x H_d_mkSelect).
     inversion H_d.
     inversion H2.
     inversion H3.
     rewrite H4 in Heqn.
     simpl in Heqn.
     Search (S _ = S _ -> _ = _).
     assert (Select_depth x1 = n).
     { apply (Nat.succ_inj _ _ Heqn). }
     symmetry in H5.
     (* specialize (IHn A x). *)
     rewrite H4.
     simpl.
     f_equal.
     + specialize (IHn (x0 + A)%type x1 H5).
       remember (Select_map (Either_map (fun x3 : A => x3)) x1) as lhs.
       rewrite <- IHn. subst lhs.
       f_equal.
       extensionality z; destruct z; trivial.
     + now rewrite fmap_id.
 Qed.

(* Program Instance Select_Applicative *)
(*         `{Functor F} : Applicative (Select F) := *)
(*   { is_functor := Select_Functor *)
(*   ; pure _ x := Pure x *)
(*   ; ap _ _ f x := Select_ap f x *)
(* }. *)

(* Program Instance Select_Selective *)
(*         `(H : Functor F) : Selective (Select F) := *)
(*   { is_applicative := Select_Applicative *)
(*   ; select _ _ x f := Select_select x f *)
(* }. *)
(* -- F1 (Free): f <$> select x y = select (fmap f <$> x) (fmap f <$> y) *)
(* f1 :: Selective f => (b -> c) -> f (Either a b) -> f (a -> b) -> f c *)
(* f1 f x y = f <$> select x y === select (fmap f <$> x) (fmap f <$> y) *)
Theorem Select_free_1 `{Functor F} :
  forall (A B C : Set) (f : B -> C) (x : Select F (A + B)) (y : Select F (A -> B)),
    Select_map f (Select_select x y) =
    Select_select (Select_map (Either_map f) x)
                  (Select_map (fun g : A -> B => f \o g) y).
Proof.
Admitted.

Theorem Select_free_1_mkSelect `{Functor F} :
  forall (A B C : Set) (f : B -> C) (x : Select F (A + B)) (y : F (A -> B)),
    Select_map f (MkSelect x y) =
    MkSelect (Select_map (Either_map f) x)
             (fmap (fun g : A -> B => f \o g) y).
Admitted.

(* -- F2 (Free): select (first f <$> x) y = select x ((. f) <$> y) *)
(* f2 :: Selective f => (a -> c) -> f (Either a b) -> f (c -> b) -> f b *)
(* f2 f x y = select (first f <$> x) y === select x ((. f) <$> y) *)
Theorem Select_free_2 `{Functor F} :
  forall (A B C : Set) (f : A -> C) (x : Select F (A + B)) (y : Select F (C -> B)),
    Select_select (Select_map (mapLeft f) x) y = Select_select x (Select_map (fun g : C -> B => g \o f) y).
Admitted.

Theorem Select_free_2_mkSelect `{Functor F} :
  forall (A B C : Set) (f : A -> C) (x : Select F (A + B)) (y : F (C -> B)),
    MkSelect (Select_map (mapLeft f) x) y = MkSelect x (fmap (fun g : C -> B => g \o f) y).
Admitted.

(* -- F3 (Free): select x (f <$> y) = select (first (flip f) <$> x) (flip ($) <$> y) *)
(* f3 :: Selective f => (c -> a -> b) -> f (Either a b) -> f c -> f b *)
(* f3 f x y = select x (f <$> y) === select (first (flip f) <$> x) (flip ($) <$> y) *)
Theorem Select_free_3 `{Functor F} :
  forall (A B C : Set)  (f : C -> A -> B)
                        (x : Select F (A + B))
                        (y : Select F C),
    Select_select x (Select_map f y) =
    Select_select (Select_map (mapLeft (flip f)) x) (Select_map rev_f_ap y).
Admitted.

Theorem Select_free_3_mkSelect `{Functor F} :
  forall (A B C : Set) (f : C -> A -> B)
                   (x : Select F (A + B))
                   (y : F C),
    MkSelect x (f <$> y) = MkSelect (Select_map (mapLeft (flip f)) x) (rev_f_ap <$> y).
Proof.
Admitted.

Lemma Either_bimap_map_comp :
  forall (A B C D E : Set)
  (f : A -> C) (g : B -> D) (h : E -> B),
  Either_bimap f g \o Either_map h = Either_bimap f (g \o h).
Proof.
  intros.
  extensionality x.
  destruct x; trivial.
Qed.

Lemma Either_bimap_right_then_left :
  forall (A B C D : Set)
  (f : A -> C) (g : B -> D),
  Either_bimap f g = mapLeft f \o Either_map g.
Proof.
  intros.
  extensionality x.
  destruct x; trivial.
Qed.

(* -- P1id (Identity): select x (pure id) == either id id <$> x *)
Theorem Select_Selective_law1 `{Functor F} :
  forall (A B : Set) (x : Select F (A + B)) (y : A -> B),
    Select_select x (Pure y) = Select_map (either y id) x.
Proof.
  intros A B x y.
  rewrite Select_select_equation_1.
  f_equal.
Qed.

Theorem Select_Applicative_law1
        `{Functor F} `{FunctorLaws F} :
  forall (A : Set) (x : Select F A), Select_ap (Pure (@id A)) x = id x.
Proof.
unfold Select_ap.
induction x.
- simpl. rewrite Select_select_equation_1. simpl.
  unfold rev_f_ap. now unfold id.
- simpl. rewrite Select_select_equation_2.
  repeat rewrite fmap_comp_x.
  repeat rewrite Select_map_comp_x.
  remember (Select_map law3_f (Pure (Left (@id A)))) as p.
  simpl in Heqp.
  subst p.  
  rewrite Select_free_3_mkSelect.
  remember (id (MkSelect x f)) as rhs.
  unfold id in Heqrhs.
  replace f with (id f) in Heqrhs by easy.
  rewrite <- fmap_id in Heqrhs.
  rewrite Select_free_3_mkSelect in Heqrhs.
  subst rhs.

  f_equal.

  remember ((mapLeft (flip (fun y : B -> A => law3_h (rev_f_ap \o y))))) as f1.
  remember (mapLeft (flip (@id (B -> A)))) as f2.

  (*...*)
  rewrite Select_free_1.
  remember (Select_map (Either_map f1) (Pure (Left (@id A)))) as q.
  simpl in Heqq.
  subst q.
  (* subst p. *)
  rewrite Select_map_comp_x.
  remember ((fun g : (A -> A) -> B * (A -> A) + A => f1 \o g) \o (law3_g \o Either_map rev_f_ap)) as p.
  rewrite Heqf1 in Heqp.
  unfold law3_h in Heqp.
  unfold law3_g in Heqp.
  unfold flip in Heqp.
  unfold comp in Heqp.
  assert ((fun (x : B + A) (x0 : A -> A) =>
          mapLeft (fun (y : B * (A -> A)) (x1 : B -> A) => uncurry (fun x2 : B => rev_f_ap (x1 x2)) y)
                  (Either_bimap (fun p : B => (p, x0)) (rev_f_ap x0) (Either_map rev_f_ap x))) =
          (fun (x : B + A) (x0 : A -> A) =>
          mapLeft (fun (y : B * (A -> A)) (x1 : B -> A) => uncurry (fun x2 : B => rev_f_ap (x1 x2)) y)
                  (Either_bimap (fun p : B => (p, x0)) (rev_f_ap x0 \o rev_f_ap) x))) as Hstep.
  { extensionality x0. extensionality x1.
    destruct x0; trivial. }
  rewrite Hstep in Heqp. clear Hstep.
  assert ((fun (x : B + A) (x0 : A -> A) =>
          mapLeft (fun (y : B * (A -> A)) (x1 : B -> A) => uncurry (fun x2 : B => rev_f_ap (x1 x2)) y)
                  (Either_bimap (fun p : B => (p, x0)) (rev_f_ap x0 \o rev_f_ap) x)) =
          (fun (x : B + A) (x0 : A -> A) =>
             (Either_bimap ((fun (y : B * (A -> A)) (x1 : B -> A) => uncurry (fun x2 : B => rev_f_ap (x1 x2)) y) \o
                            (fun p : B => (p, x0))) (rev_f_ap x0 \o rev_f_ap) x))) as Hstep.
  { extensionality x0. extensionality y0. destruct x0; trivial. }
  rewrite Hstep in Heqp. clear Hstep.
  (*...*)
  rewrite Select_free_3.
  remember (Select_map (mapLeft (flip p)) (Pure (Left (@id A)))) as q.
  subst p.
  simpl in Heqq.
  unfold flip in Heqq.
  unfold comp in Heqq.
  unfold rev_f_ap in Heqq.
  unfold id in Heqq.
  compute in Heqq.
  subst q.
  assert ((fun x0 : B + A => match x0 with
                                  | Left a => Left (fun x1 : B -> A => x1 a)
                                  | Right x1 => Right x1
                                  end) =
          (mapLeft rev_f_ap) \o id) as Hstep by reflexivity.
  rewrite Hstep. clear Hstep. clear Heqf1 f1.
  remember (Pure (Left (mapLeft rev_f_ap \o id))) as p.
  (* assert (p = *)
  (*         Pure (mapLeft (comp (mapLeft rev_f_ap)) (Left id))) as Hstep by trivial. *)
  assert (p =
          Select_map (mapLeft (comp (mapLeft rev_f_ap))) (Pure (Left (@id (B + A)%type)))) as Hstep by trivial.
  clear Heqp. rewrite Hstep. clear Hstep p.
  (*...*)
  replace (id x) with x in IHx by reflexivity.
  rewrite <- IHx at 2.
  rewrite Select_free_1.
  rewrite Heqf2.
  repeat rewrite Select_map_comp_x.
  remember (Either_map (mapLeft (flip (@id (B -> A)%type))) \o Left) as q.

  remember (Select_select (Select_map q (Pure (@id (B+A)%type)))
    (Select_map ((fun g : (B + A -> B + A) -> B + A => mapLeft (flip (@id (B -> A))) \o g) \o rev_f_ap) x)) as rhs.
  rewrite Select_free_3 in Heqrhs.
  subst rhs. subst q.
  f_equal.
Qed.

(* pure f <*> pure x = pure (f x)   *)
Theorem Select_Applicative_law2
        `{Functor F} `{FunctorLaws F} :
  forall (A B : Set) (f : A -> B) (x : A), Select_ap (Pure f) (Pure x) = Pure (f x).
Proof.
  intros A B f x.
  unfold Select_ap.
  simpl.
  rewrite Select_select_equation_1.
  now simpl.
Qed.

Theorem Select_Applicative_ap_fmap
        `{Functor F} `{FunctorLaws F} :
  forall (A B : Set) (f : A -> B) (x : Select F A), Select_map f x = Select_ap (Pure f) x.
Proof.
  intros A B f x.
  revert f.
  generalize dependent B.
  generalize dependent A.
  induction x; intros.
  - simpl. now rewrite Select_Applicative_law2.
  - unfold Select_ap. simpl.
    rewrite Select_select_equation_2.
    simpl.
    rewrite Select_map_comp_x.
    rewrite Select_free_3.
    remember (Select_select (Select_map (mapLeft (flip (law3_g \o Either_map rev_f_ap))) (Pure (Left f0)))
       (Select_map rev_f_ap x)) as p.
    simpl in Heqp.
    assert (Select_select (Pure (Left (flip (law3_g \o Either_map rev_f_ap) f0))) (Select_map rev_f_ap x) =
            Select_select (Select_map Left (Pure (flip (law3_g \o Either_map rev_f_ap) f0))) (Select_map rev_f_ap x))
      as Hstep by reflexivity.
    rewrite Hstep in Heqp. clear Hstep.
    remember (flip (law3_g \o Either_map rev_f_ap) f0) as q.
    Print Select_ap.
    assert (p = Select_ap (Pure q) x) as Hstep.
    { rewrite Heqq. rewrite Heqp. unfold Select_ap. rewrite Heqq. reflexivity. }
    rewrite Hstep. clear Hstep Heqp p.
    rewrite IHx.
    subst q.
    rewrite fmap_comp_x.
    remember (MkSelect (Select_ap (Pure (Either_map f0)) x) (fmap[ F] (fun k : B -> A => f0 \o k) f)) as lhs.
    remember (MkSelect (Select_ap (Pure (flip (law3_g \o Either_map rev_f_ap) f0)) x)
                       (fmap[ F] (fun y : B -> A => law3_h (rev_f_ap \o y)) f) ) as rhs.
    rewrite Select_free_3_mkSelect in Heqlhs.
    rewrite Select_free_3_mkSelect in Heqrhs.
    subst rhs lhs.
    f_equal.
    replace (Pure (Either_map f0)) with (Select_map (const (Either_map (E:=B) f0)) (Pure (@id A))) by reflexivity.
    replace (Pure (flip (law3_g \o Either_map rev_f_ap) f0)) with
            (Select_map (const (flip (law3_g \o Either_map (E:=B) rev_f_ap) f0)) (Pure (@id A))) by reflexivity.
    remember (Select_map (mapLeft (flip (fun k : B -> A => f0 \o k)))
                         (Select_ap (Select_map (const (Either_map f0)) (Pure (@id A))) x)) as lhs.
    remember (Select_map (mapLeft (flip (fun y : B -> A => law3_h (rev_f_ap \o y))))
             (Select_ap (Select_map (const (flip (law3_g \o Either_map rev_f_ap) f0)) (Pure (@id A))) x)) as rhs.
    unfold Select_ap in *.
    rewrite Select_free_1 in Heqlhs.
    rewrite Select_free_1 in Heqrhs.
    repeat rewrite Select_map_comp_x in Heqlhs.
    repeat rewrite Select_map_comp_x in Heqrhs.
    rewrite Select_free_3 in Heqlhs.
    rewrite Select_free_3 in Heqrhs.
    subst lhs rhs.
    f_equal.
    repeat rewrite Select_map_comp_x.
    compute. do 2 f_equal.
    extensionality x0; destruct x0; trivial.
 Qed.

Theorem Select_pure_left `{HF : Functor F} {HFL : FunctorLaws F} :
  forall (A B : Set) (x : A) (y : Select F (A -> B)),
    Select_select (Pure (Left x)) y = Select_map (rev_f_ap x) y.
Proof.
  intros A B x y.
  (* The idea of the proof is to massage the goal into the form of the definition of Select_ap,
     fold the definition, substitute it with the applicative <*> and finish the prove using
     the Applicative laws. *)

  (* First, we use fmap_id to append an id application to the second argument of select *)
  assert ( Select_select (Pure (Left x)) y =
           Select_select (Pure (Left x)) (Select_map id y)) as H.
  { now rewrite Select_Functor_law1. } 
  rewrite H. clear H.
  (* Now we use the third Selective Free Theorem to transfer the newly created id to the first argument
     of select and leave the second fmap'ed by the reverse function application *)
  rewrite Select_free_3.
  (* Drag the id inside Pure *)
  remember (Select_map (mapLeft (flip (@id (A -> B)))) (Pure (Left x))) as p.
  compute in Heqp.
  rewrite Heqp. clear Heqp p.
  (* Use ap_homo to extract Left (aka Left) from Pure *)
  assert (Select_select (Pure (Left (fun x0 : A -> B => x0 x))) (Select_map rev_f_ap y) =
          Select_select (Select_ap (Pure Left) (Pure (fun x0 : A -> B => x0 x))) (Select_map rev_f_ap y)) as H.
  { now rewrite Select_Applicative_law2. }
  rewrite H. clear H.
  (* Use ap_fmap to rewrite `pure Left <*>` as `Left <$>` *)
  replace (Select_ap (Pure Left) (Pure (fun x0 : A -> B => x0 x))) with
          (Select_map (@Left ((A -> B) -> B) B) (Pure (fun x0 : A -> B => x0 x))) by
      now rewrite <- Select_Applicative_ap_fmap.
  (* Fold reverse function application *)
  assert ((fun x0 : A -> B => x0 x) = rev_f_ap x) as H by reflexivity.
  rewrite H. clear H.
  (* Unfold <*? to make the goal identical to Select_ap definition *)
  replace (Select_select (Select_map Left (Pure (rev_f_ap x))) (Select_map rev_f_ap y)) with
          (Select_ap (Pure (rev_f_ap x)) y) by reflexivity.
  (* Use the rigidness of the freer selective construction, i.e. the fact that
     Select_ap == apS == (<*>) *)
  now rewrite Select_Applicative_ap_fmap.
Qed.

(* u <*> pure y = pure ($ y) <*> u *)
Theorem Select_Applicative_law3
        `{Functor F} `{FunctorLaws F} :
  forall (A B : Set) (u : Select F (A -> B)) (y : A), Select_ap u (Pure y) = Select_ap (Pure ((fun f => f y))) u.
Proof.
  intros A B u y.
  destruct u.
  - unfold Select_ap. simpl.
    now repeat rewrite Select_select_equation_1.
  - unfold Select_ap. simpl.
    rewrite Select_select_equation_1.
    rewrite Select_select_equation_2.
    simpl.
    repeat rewrite Select_map_comp_x.
    remember ((Either_map (either (rev_f_ap y) id) \o Either_map Left)) as p.
    assert (p = Either_map ((rev_f_ap y))) as Hstep.
    { rewrite Heqp. extensionality z. destruct z; trivial. }
    rewrite Hstep. clear Hstep Heqp p.
    repeat rewrite fmap_comp_x.
    remember ((fun y0 : B0 -> A -> B => either (rev_f_ap y) id \o (Left \o y0))) as p.
    remember ((fun y0 : B0 -> A -> B => law3_h (rev_f_ap \o y0))) as q.
    remember ( MkSelect (Select_map (Either_map (rev_f_ap y)) u) (fmap[ F] p f)) as lhs.
    rewrite Select_free_3_mkSelect in Heqlhs.
    subst lhs.
    remember (MkSelect (Select_select (Pure (Left (fun f0 : A -> B => f0 y))) (Select_map (law3_g \o Either_map rev_f_ap) u)) (fmap[ F] q f)) as rhs.
    rewrite Select_free_3_mkSelect in Heqrhs.
    rewrite Select_free_1 in Heqrhs.
    subst rhs.
    f_equal.
    simpl.
    repeat rewrite Select_map_comp_x.
    (* select (pure (Left  x)) y = ($x) <$> y *)
    rewrite Select_pure_left.
    rewrite Select_map_comp_x.
    f_equal.
    rewrite Heqp. clear Heqp p. rewrite Heqq. clear Heqq q.
    compute. extensionality x. destruct x; trivial.
Qed.

Theorem Select_Applicative_law4
        `{Functor F} `{FunctorLaws F} :
  forall (A B C : Set) (v : Select F (A -> B)) (u : Select F (B -> C))
    (w : Select F A),
  (* pure (fun (f : b -> c) (g : a -> b) (x : a) => f (g x)) <*> u <*> v <*> w = u <*> (v <*> w) *)
  Select_ap (Select_ap (Select_ap (Pure (fun (f : B -> C) (g : A -> B) (x : A) => f (g x))) u) v) w =
  Select_ap u (Select_ap v w).
Proof.
  intros A B C v u w.
  generalize dependent C.
  generalize dependent B.
  generalize dependent A.
  induction w; intros.
  - rewrite Select_Applicative_law3.
    rewrite Select_Applicative_law3.
    unfold Select_ap. simpl.
    repeat rewrite Select_pure_left. repeat rewrite Select_map_comp_x.
    rewrite Select_free_1. repeat rewrite Select_map_comp_x.
    remember (Either_map (rev_f_ap (fun f : A -> C => f a) \o rev_f_ap) \o
        ((Left \o rev_f_ap (fun (f : B -> C) (g : A -> B) (x : A) => f (g x))) \o rev_f_ap)) as p.
    remember ((fun g : ((A -> B) -> A -> C) -> A -> C => (rev_f_ap (fun f : A -> C => f a) \o rev_f_ap) \o g) \o rev_f_ap) as q.
    remember ((rev_f_ap \o rev_f_ap (fun f : A -> B => f a)) \o rev_f_ap) as r.
    remember (Select_select (Select_map p u) (Select_map q v)) as lhs.
    remember (Select_select (Select_map Left u) (Select_map r v)) as rhs.
    rewrite Select_free_3 in Heqlhs.
    rewrite Select_free_3 in Heqrhs.
    subst lhs rhs.
    f_equal.
    repeat rewrite Select_map_comp_x.
    subst p q r.
    f_equal.
  - unfold Select_ap. simpl.
    repeat rewrite Select_select_equation_2.
    simpl. repeat rewrite Select_select_equation_2.
    repeat rewrite Select_map_comp_x.
    repeat rewrite fmap_comp_x.

    rewrite Select_pure_left.
    repeat rewrite Select_map_comp_x.
    remember ( MkSelect
    (Select_select
       (Select_map (law3_f \o Left)
          (Select_select
             (Select_map ((Left \o rev_f_ap (fun (f0 : B0 -> C) (g : A -> B0) (x : A) => f0 (g x))) \o rev_f_ap) u)
             (Select_map rev_f_ap v))) (Select_map (law3_g \o Either_map rev_f_ap) w))
    (fmap[ F] (fun y : B -> A => law3_h (rev_f_ap \o y)) f)) as lhs.
    remember (MkSelect
    (Select_select (Select_map (law3_f \o Left) u)
       (Select_map (law3_g \o Either_map rev_f_ap)
          (Select_select (Select_map (law3_f \o Left) v) (Select_map (law3_g \o Either_map rev_f_ap) w))))
    (fmap[ F] (fun y : B -> A => law3_h (rev_f_ap \o law3_h (rev_f_ap \o y))) f)) as rhs.
    rewrite Select_free_3_mkSelect in Heqlhs.
    rewrite Select_free_3_mkSelect in Heqrhs.
    subst lhs rhs.
    f_equal.
    remember (Select_map (law3_f \o Left)
          (Select_select
             (Select_map ((Left \o rev_f_ap (fun (f0 : B0 -> C) (g : A -> B0) (x : A) => f0 (g x))) \o rev_f_ap) u)
             (Select_map rev_f_ap v))) as p1.
    remember (Select_map (law3_g \o Either_map rev_f_ap) w) as q1.
    remember (Select_map (law3_f \o Left) u) as p2.
    remember (Select_map (law3_g \o Either_map rev_f_ap)
          (Select_select (Select_map (law3_f \o Left) v) (Select_map (law3_g \o Either_map rev_f_ap) w))) as q2.
    do 2 rewrite Select_free_1.
    subst p1 q1 p2 q2.
    repeat rewrite Select_map_comp_x.
    unfold flip.
    remember (Either_map (mapLeft (fun (y : B * (A -> C)) (x : B -> A) => law3_h (rev_f_ap \o x) y)) \o
                         (law3_f \o Left)) as p.
    remember (Either_map
          (mapLeft
             (fun (y : B * (A -> B0) * (B0 -> C)) (x : B -> A) => law3_h (rev_f_ap \o law3_h (rev_f_ap \o x)) y)) \o
        (law3_f \o Left)) as q.
    remember ((fun g : (B0 -> C) -> B * (A -> B0) * (B0 -> C) + C =>
         mapLeft (fun (y : B * (A -> B0) * (B0 -> C)) (x : B -> A) => law3_h (rev_f_ap \o law3_h (rev_f_ap \o x)) y) \o
         g) \o (law3_g \o Either_map rev_f_ap)) as r.
    remember (Select_select (Select_map q u)
    (Select_map r (Select_select (Select_map (law3_f \o Left) v) (Select_map (law3_g \o Either_map rev_f_ap) w)))) as rhs.
    rewrite Select_free_1 in Heqrhs.
    subst rhs.
    repeat rewrite Select_map_comp_x.
    (* Looks like this proof boils down to the Selective associativity law *)
Admitted.

Lemma Either_mapLeft_comp :
  forall (A B C D : Set)
    (x : (A + B))
    (g : (A -> C))
    (f : (C -> D)),
    mapLeft f (mapLeft g x) = mapLeft (f \o g) x.
Proof.
  intros A B C D x f.
  destruct x; trivial.
Qed.

Lemma Either_mapLeft_right :
  forall (A B C : Set)
    (x : (A + B))
    (f : (A -> C)),
    mapLeft f (Either_map (@Right A B) x) = Either_map Right (mapLeft f x).
Proof.
  intros A B C x f.
  destruct x; trivial.
Qed.

(* -- P1id (Identity): select x (pure id) == either id id <$> x *)
Theorem Select_Selective_law1 `{Functor F} :
  forall (A B : Set) (x : Select F (A + B)) (y : A -> B),
    Select_select x (Pure y) = Select_map (either y id) x.
Proof.
  intros A B x y.
  rewrite Select_select_equation_1.
  f_equal.
Qed.

Theorem select_selective_law3_assoc :
  forall (A B C : Set) `{FunctorLaws F}
  (x : Select F (B + C))
  (y : Select F (A + (B -> C)))
  (z : Select F (A -> B -> C)),
  Select_select x (Select_select y z) =
  Select_select (Select_select (Select_map law3_f x) (Select_map law3_g y)) (Select_map law3_h z).
Proof.
  intros A B C F HF HFL x y z.
  revert z y x.
  remember (A -> B -> C) as T.
  induction z.
  - admit.
  - 
(* Lemma select_selective_law3_assoc_ind_step : *)
(*   forall (A B C : Type) *)
(*     (x  : Select F (A + B)) *)
(*     (y : Select F (X -> B)) *)
(*     (x' : Select F (X + (A + B)) (y' : Select F (A -> B)) *)
(*   select x y = MkSelect x' y' *)

(* Theorem select_selective_law3_assoc : *)
(*   forall (A B C : Type) `{FunctorLaws F} *)
(*   (x : Select F (B + C)) *)
(*   (y : Select F (A + (B -> C))) *)
(*   (z : Select F (A -> B -> C)), *)
(*   x <*? (y <*? z) = (law3_f <$> x) <*? (law3_g <$> y) <*? (law3_h <$> z). *)
(*   (* Select_select x (Select_select y z) = *) *)
(*   (* Select_select (Select_select (Select_map law3_f x) (Select_map law3_g y)) (Select_map law3_h z). *) *)
(* Proof. *)
(*   intros A B C F HF HFL x y z. *)
(*   dependent induction z. *)
(*   - admit. *)
(*   - remember (x <*? (y <*? MkSelect z f)) as lhs. *)
(*     remember (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y <*? fmap[ Select F] law3_h (MkSelect z f)) as rhs. *)
(*     simpl in *. *)
(*     rewrite Select_select_equation_2 in Heqlhs. *)
(*     rewrite Select_select_equation_2 in Heqlhs. *)
(*     rewrite Select_select_equation_2 in Heqrhs. *)
(*     repeat rewrite Select_select_to_infix in *. repeat rewrite Select_map_to_fmap in *. *)
(*     repeat rewrite Either_map_to_fmap in *. *)
(*     rewrite Heqlhs. rewrite Heqrhs. clear Heqlhs lhs Heqrhs rhs. *)
(*     repeat rewrite fmap_comp_x. *)
(*     remember (  MkSelect *)
(*     (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g (fmap[ Select F] law3_f y <*? fmap[ Select F] law3_g z)) *)
(*     (fmap[ F] (fun y0 : B0 -> A -> B -> C => law3_h (law3_h y0)) f)) as lhs. *)
(*     remember  (MkSelect *)
(*     (fmap[ Select F] law3_f (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y) <*? *)
(*      fmap[ Select F] (fun y0 : B0 + (A -> B -> C) => law3_g (fmap[ sum B0] law3_h y0)) z) *)
(*     (fmap[ F] (fun y0 : B0 -> A -> B -> C => law3_h (law3_h \o y0)) f)) as rhs. *)
(*     rewrite Select_free_3_mkSelet in Heqlhs. *)
(*     rewrite Select_free_3_mkSelet in Heqrhs. *)
(*     rewrite Heqlhs. rewrite Heqrhs. clear Heqlhs lhs Heqrhs rhs. *)
(*     f_equal. *)

(*     remember (fmap[ Select F] law3_g (fmap[ Select F] law3_f y <*? fmap[ Select F] law3_g z)) as q1. *)
(*     remember (fmap[ Select F] (mapLeft (flip (fun y0 : B0 -> A -> B -> C => law3_h (law3_h \o y0)))) *)
(*     (fmap[ Select F] law3_f (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y) <*? *)
(*      fmap[ Select F] (fun y0 : B0 + (A -> B -> C) => law3_g (fmap[ sum B0] law3_h y0)) z)) as rhs. *)
(*     remember (mapLeft (flip (fun y0 : B0 -> A -> B -> C => law3_h (law3_h \o y0)))) as t. *)
(*     rewrite Select_free_1 in Heqrhs. *)
(*     rewrite Heqt in Heqrhs. clear Heqt t. *)
(*     remember ( fmap[ Select F] *)
(*              (fun g : A * B -> B0 * (A * B) + C => *)
(*               mapLeft (flip (fun y0 : B0 -> A -> B -> C => law3_h (law3_h \o y0))) \o g) *)
(*              (fmap[ Select F] (fun y0 : B0 + (A -> B -> C) => law3_g (fmap[ sum B0] law3_h y0)) z)) as q2. *)

(*     remember ((mapLeft (flip (fun y0 : B0 -> A -> B -> C => law3_h (law3_h y0))))) as p1. *)
(*     remember ((mapLeft (flip (fun y0 : B0 -> A -> B -> C => law3_h (law3_h \o y0))))) as p2. *)
(*     remember (  fmap[ Select F] p1 *)
(*                     (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g (fmap[ Select F] law3_f y <*? fmap[ Select F] law3_g z)) ) as lhs. *)
(*     remember ( fmap[ Select F] p2 *)
(*     (fmap[ Select F] law3_f (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y) <*? *)
(*          fmap[ Select F] (fun y0 : B0 + (A -> B -> C) => law3_g (fmap[ sum B0] law3_h y0)) z)) as rhs. *)
(*     rewrite Select_free_1 in Heqlhs. *)
(*     rewrite Select_free_1 in Heqrhs. *)
(*     rewrite fmap_comp_x in Heqlhs. *)
(*     rewrite fmap_comp_x in Heqrhs. *)
(*     rewrite Select_free_1 in Heqrhs. *)
(*     repeat rewrite fmap_comp_x in Heqrhs. *)
(*     (* Looks like a sensible goal *) *)
(*     rewrite Heqlhs. rewrite Heqrhs. clear Heqlhs lhs Heqrhs rhs. *)

(*     remember (fmap[ Select F] (fun y0 : B + C => fmap[ sum B] p1 (law3_f y0)) x) as x1'. *)
(*     remember (fmap[ Select F] *)
(*     (fun y0 : B + C => fmap[ sum B] (fun y1 : A * B + C => fmap[ sum (A * B)] p2 (law3_f y1)) (law3_f y0)) x) as x2'. *)
(*     remember (fmap[ Select F] (fun g : B -> B0 * A * B + C => p1 \o g) *)
(*     (fmap[ Select F] law3_g (fmap[ Select F] law3_f y) *)

(*     rewrite Heqp1. clear Heqp1 p1. rewrite Heqp2. clear Heqp2 p2. *)
(*     remember ( mapLeft (flip (fun y0 : B0 -> A -> B -> C => law3_h (law3_h \o y0)))) as t. *)
(*     setoid_rewrite <- Heqt. *)

(*     remember (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g (fmap[ Select F] law3_f y <*? fmap[ Select F] law3_g z)) as p. *)
(*     remember (fmap[ Select F] law3_f (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y) <*? *)
(*                   fmap[ Select F] (fun y0 : B0 + (A -> B -> C) => law3_g (fmap[ sum B0] law3_h y0)) z) as q. *)
(*     unfold law3_h in *. *)
(*     assert (forall A B C (x : A) (y : B) (z : C), pair x (pair y z) = pair (pair x y) z). *)

Definition reassoc_triple {A B C : Type}
    (p : (A * (B * C))) : (A * B * C) :=
  match p with
  | pair x (pair y z) => pair (pair x y) z
  end.

(* Lemma lemma1: *)
(*   forall (F : Type -> Type) (HF : Functor F) (HFL : FunctorLaws F) *)
(*     (A B C B0 : Type) *)
(*     (z : Select F (B0 + (A -> B -> C))), *)
(*     (F (B0 -> A -> B -> C) -> *)
(*                  forall H : Functor F, *)
(*                    FunctorLaws F -> *)
(*                    forall (x : Select F (B + C)) (y : Select F (A + (B -> C))) *)
(*                           (t : A * B + C -> (B0 + (A -> B -> C) -> B0 * (A * B) + C) + (B0 * (A * B) + C)), *)
(*                      t = *)
(*                      (fun y0 : A * B + C => *)
(*                         mapLeft *)
(*                           (fun (y1 : A * B) (x0 : B0 + (A -> B -> C)) => *)
(*                              Either_bimap (fun p : B0 => (p, y1)) (fun f0 : A -> B -> C => law3_h f0 y1) x0) (law3_f y0)) -> *)
(*                      fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g (fmap[ Select F] law3_f y <*? fmap[ Select F] law3_g z) = *)
(*                      fmap[ Select F] (mapLeft reassoc_triple) *)
(*                          (fmap[ Select F] t (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y) <*? fmap[ Select F] rev_f_ap z). *)
(*     Proof. *)
(*       intros F A B C B0 z f H H0 x y t Heqt *)
(* Theorem select_selective_law3_silly : *)
(*   forall (A B C T1 T2 T3 : Type) `{FunctorLaws F} *)
(*   (E1 : T1 = (B + C)%type) *)
(*   (E2 : T2 = (A + (B -> C))%type) *)
(*   (E3 : T3 = (A -> B -> C)) *)
(*   (x : Select F T1) *)
(*   (y : Select F T2) *)
(*   (z : Select F T3), *)
(*   x <*? (y <*? z) = x <*? (y <*? z). *)
(* Proof. *)
(*   intros A B C F HF HFL x y z. *)
(*   (* remember (A -> B -> C) as T3. *) *)
(*   revert x y z. *)
(*   generalize dependent C. *)
(*   generalize dependent B. *)
(*   generalize dependent A. *)

(*   (* remember (A + (B -> C))%type as T2. *) *)
(*   (* remember (B + C)%type as T1. *) *)
(*   induction z. *)

(* Theorem select_selective_law3_ind_z : *)
(*   forall (A B C : Type) `{FunctorLaws F} *)
(*   (x : Select F (B + C)) *)
(*   (y : Select F (A + (B -> C))) *)
(*   (z : Select F (A -> B -> C)), *)
(*   x <*? (y <*? z) = (law3_f <$> x) <*? (law3_g <$> y) <*? (law3_h <$> z). *)
(* Proof. *)
(*   intros A B C F HF HFL x y z. *)
(*   refine (Select_ind). *)
(*   pose (Select_ind) as Ind. *)
(*   specialize (Ind F). *)
(*   Check @MkSelect. *)
(*   refine (match z with *)
(*           | Pure a => _ *)
(*           | @MkSelect _ _ T c d => _ *)
(*           end). *)
(*   - admit. *)
(*   -  *)

(* Theorem select_selective_law3_assoc : *)
(*   forall (A B C : Type) `{FunctorLaws F} *)
(*   (x : Select F (B + C)) *)
(*   (y : Select F (A + (B -> C))) *)
(*   (z : Select F (A -> B -> C)), *)
(*   x <*? (y <*? z) = (law3_f <$> x) <*? (law3_g <$> y) <*? (law3_h <$> z). *)
(*   (* Select_select x (Select_select y z) = *) *)
(*   (* Select_select (Select_select (Select_map law3_f x) (Select_map law3_g y)) (Select_map law3_h z). *) *)
(* Proof. *)
(*   intros A B C F HF HFL x y z. *)
(*   dependent induction z generalizing x y. *)
(*   - admit. *)
(*   - specialize (IHx A B0 (B + C)%type x eq_refl). *)
(*     remember (fmap[ Select F] law3_g y) as y'. *)
(*     remember (fmap[ Select F] law3_h z) as z'. *)

Scheme Select_ind' := Minimality for Select Sort Prop.

Print Select_ind.

Theorem select_selective_law3_assoc :
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

    remember (fmap[ Select F] t
      (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y) <*? fmap[ Select F] rev_f_ap z) as q.
    remember (fmap[ Select F] law3_g (fmap[ Select F] law3_f y <*? fmap[ Select F] law3_g z)) as p.
    repeat rewrite fmap_comp_x in Heqx''.
    apply (f_equal id).

      

    Specialize (IHz).
    rewrite Select_free_2_mkSelet in Heqlhs.
    rewrite Select_free_2_mkSelet in Heqrhs.
    remember (fmap[ Select F] law3_f x <*?
              fmap[ Select F] law3_g (fmap[ Select F] law3_f y <*? fmap[ Select F] law3_g z)) as p1.
    remember (fmap[ Select F] law3_f (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y) <*?
              fmap[ Select F] (fun y0 : B0 + (A -> B -> C) => law3_g (fmap[ sum B0] law3_h y0)) z) as p2.
    remember (fmap[ F]
                (fun g : ((B0 -> A -> B -> C) -> C) -> C =>
                 g \o flip (fun y0 : B0 -> A -> B -> C => law3_h (law3_h y0))) (fmap[ F] rev_f_ap f)) as q1.
    remember (fmap[ F]
                (fun g : ((B0 -> A -> B -> C) -> C) -> C =>
                 g \o flip (fun y0 : B0 -> A -> B -> C => law3_h (law3_h \o y0))) (fmap[ F] rev_f_ap f)) as q2.

Admitted.

Definition reassoc_triple {A B C : Type}
    (p : (A * (B * C))) : (A * B * C) :=
  match p with
  | pair x (pair y z) => pair (pair x y) z
  end.

Definition reassoc_triple' {A B C : Type}
    (p : (A * (B * C)) + (A * B * C)) : (A * B * C) :=
  match p with
  | Left (pair x (pair y z)) => pair (pair x y) z
  | inr q                   => q
  end.

Lemma t : forall (A B C : Type)
  (x : A) (y : B) (z : C),
  pair (pair x y) z = reassoc_triple (pair x (pair y z)).
Proof. trivial. Qed.

    rewrite Heqlhs. rewrite Heqrhs. clear Heqlhs lhs Heqrhs rhs.
    f_equal.
    remember (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g (fmap[ Select F] law3_f y <*? fmap[ Select F] law3_g z)) as q1.
    remember (fmap[ Select F] law3_f (fmap[ Select F] law3_f x <*? fmap[ Select F] law3_g y) <*?
     fmap[ Select F] (fun y0 : B0 + (A -> B -> C) => law3_g (fmap[ sum B0] law3_h y0)) z) as q2.


