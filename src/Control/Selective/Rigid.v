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

Inductive Select (f : Type -> Type) (a : Type) :=
    Pure   : a -> Select f a
  | MkSelect : forall b, Select f (b + a) -> f (b -> a) -> Select f a.

Arguments Pure {f} {a}.
Arguments MkSelect {f} {a} {b}.

(* Fixpoint Select_map {A B : Type} {F : Type -> Type} `{Functor F} *)
(*            (f : (B -> A)) (x : Select F B) : Select F A := *)
(*   match x with *)
(*   | Pure a => Pure (f a) *)
(*   | MkSelect x y => MkSelect (Select_map (fmap f) x) ((fun g => compose f g) <$> y) *)
(*   end. *)

Fixpoint Select_map {A B : Type} {F : Type -> Type} `{Functor F}
           (f : (A -> B)) (x : Select F A) : Select F B :=
  match x with
  | Pure a => Pure (f a)
  | MkSelect x y => MkSelect (Select_map (Either_map f) x)
                             ((fun k : _ -> A => f \o k) <$> y)
  end.

Program Instance Select_Functor (F : Type -> Type)
  `{Functor F} : Functor (Select F) := {
  fmap := fun _ _ f x => Select_map f x
}.

Definition id_f {A : Type} (x : A) := x.

Lemma id_x_is_x {A : Type}:
  forall (x : A), id x = x.
Proof.
  intros x. reflexivity.
Qed.

Lemma compose_id {A B : Type}:
  forall (f : A -> B), (compose f id) = f.
Proof.
  intros f.
  extensionality x.
  unfold compose.
  rewrite id_x_is_x.
  reflexivity.
Qed.

Lemma Either_map_id {E X : Type} : Either_map (E:=E) (@id X) = id.
Proof.
  extensionality x.
  destruct x;
  reflexivity.
Qed.

Lemma Either_map_comp {E A B C : Type} :
  forall (f : B -> C) (g : A -> B),
  Either_map (E:= E) f \o Either_map g = Either_map (f \o g).
Proof.
  intros f g.
  extensionality x.
  destruct x; reflexivity.
Qed.

Import FunctorLaws.

(* Lemma Select_Either_map_commute {E A B : Type} `{Functor F} : *)
(*   forall (x : Select F (E + A)) (f : A -> B), *)
(*   Select_map (Either_map f) x = Either_map (Select_map f) x. *)

(* Select_map (Either_map f) (Select_map (Either_map g) XX) = *)
(*   Select_map (Either_map (f \o g)) XX *)

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
extensionality XX.
induction XX.
- reflexivity.
- simpl.
  f_equal.
  * rewrite Either_map_id.
    apply IHXX.
  * setoid_rewrite compose_id. (* rewrite under the fun binder *)
    rewrite fmap_id.
    reflexivity.
Qed.
(* Theorem Select_Functor_law2 {A B C : Type} *)
(*         `{Functor F} `{FunctorLaws F} : *)
(*   forall (f : B -> C) (g : A -> B) (x : Select F A), *)
(*   ((Select_map f) \o (Select_map g)) x = Select_map (f \o g) x. *)
Obligation 2.
extensionality x.
induction x as [|a B x IHx].
- reflexivity.
- simpl in *.
  f_equal.
  + rewrite <- Either_map_comp.
    pose (g' : B + a -> b := fun y => match y with
                                      | Left e => ) 
    
(* extensionality x. *)
(* induction x as [|a B x IHx]. *)
(* - reflexivity. *)
(* - simpl in *. *)
(*   f_equal. *)
(*   + destruct IHx. *)

(*     rewrite <- Either_map_comp. *)
(*     Check Select_ind. *)

    (* pose (z := @Either_map b0 a b g). *)
    (* assert (z = Either_map g). *)
    (* { reflexivity. } *)
    (* rewrite <- H1. *)
    (* pose (thing1 := fmap (fun f : b0 -> a => g \o f) f0). *)
    (* pose (thing2 := Select_map (either id g) XX).  *)
    
  + rewrite fmap_rewrite_compose.
    rewrite fmap_comp.
    f_equal.

simpl.
induction XX.
- reflexivity.
- simpl. f_equal.
  + rewrite <- Either_map_comp.
    rewrite IHXX with (g := (Either_map g)).
  + rewrite fmap_rewrite_compose.
    rewrite fmap_comp.
    f_equal.
(* Obligation 2. *)
(* extensionality XX. *)
(* simpl. *)
(* induction XX. *)
(* - reflexivity. *)
(* - simpl. f_equal. *)
(*   + rewrite <- Either_map_comp. *)
(*     rewrite IHXX with (g := (Either_map g)). *)
(*   + rewrite fmap_rewrite_compose. *)
(*     rewrite fmap_comp. *)
(*     f_equal. *)
    

Definition law3_f {A B C : Type}
           (x : B + C) : B + (A + C) := Right <$> x.

Definition law3_g {A B C : Type}
           (y : A + (B -> C)) : B -> A * B + C :=
  fun a => Either_bimap (fun p => pair p a) (fun f => f a) y.

Definition law3_h  {A B C : Type}
           (f : A -> B -> C) : A * B -> C :=
  fun p => match p with
           | pair x y => f x y
           end.

(* Fixpoint Select_select_old {A B : Type} {F : Type -> Type} `{FF : Functor F} *)
(*          (x : Select F (B + A)) (f : Select F (B -> A)) {struct f} : Select F A := *)
(*   match f with *)
(*   | Pure y                    => either y id <$> x *)
(*   | MkSelect y z => *)
(*     MkSelect (Select_select_old (Select_map law3_f x) *)
(*                                 (law3_g <$> y)) *)
(*              (law3_h <$> z) *)
(*   end. *)


(* ?O(n)? select implementation *)
Fixpoint Select_select_go {A B C : Type} `{Functor F}
         (x : Select F (A + B)) (s : Select F C) (k : C -> (A -> B)) {struct s} :
         Select F B :=
  match s with
  | Pure y => either (k y) id <$> x
  | MkSelect y z =>
    MkSelect (Select_select_go (law3_f <$> x)
                               y
                               (compose law3_g (mapRight k))
             )
             (compose law3_h (compose k) <$> z)
  end.

Fixpoint Select_select  {A B : Type} `{Functor F}
         (x : Select F (B + A)) (f : Select F (B -> A)) : Select F A :=
  Select_select_go x f id.

    (* select x (Select y z) = Select (select (f <$> x) (g <$> y)) (h <$> z) *)
    (*   where *)
    (*     f x = Right <$> x *)
    (*     g y = \a -> bimap (,a) ($a) y *)
    (*     h z = uncurry z *)

Definition Select_ap {A B : Type} {F : Type -> Type} `{Functor F}
           (t : Select F (A -> B)) (x : Select F A) : Select F B :=
  Select_select (Left <$> t) ((fun y f => f y) <$> x).

Program Instance Select_Applicative
        (F : Type -> Type) `{Functor F} : Applicative (Select F) :=
  { is_functor := Select_Functor F
  ; pure _ x := Pure x
  ; ap _ _ f x := Select_ap f x
}.

Program Instance Select_Selective (F : Type -> Type) `{Functor F}: Selective (Select F) :=
  { is_applicative := Select_Applicative F
    ; select _ _ x f := Select_select x f
  }.

(******************** Selective laws *****************************)
Theorem select_selective_law1_identity
  {A : Type} {F : Type -> Type} `{Functor F} {x : Select F (Either A A)} :
  x <*? (pure id) = either id id <$> x.
Proof.
    destruct x.
  - simpl.
    reflexivity.
  - destruct x;
    simpl;
    reflexivity.
Qed.

Lemma pure_eq_pure {A B : Type} {F : Type -> Type} {x y : A} :
  @Pure F A x = @Pure F A y -> x = y.
Proof.
  intros H.
  congruence.
Qed.

Theorem select_selective_law2_distr
  {A B : Type} {F : Type -> Type} `{Functor F}
  (x : (Either A B))
  (y : Select F (A -> B))
  (z : Select F (A -> B)) :
  pure x <*? (y *> z) = (pure x <*? y) *> (pure x <*? z).
Proof.
  simpl pure.
  destruct x.
  - induction y.
  
  (* destruct x. *)
  (* - simpl. *)
  (*   destruct y. *)
  (*   -- simpl. *)
  (*      destruct z. *)
  (*      --- simpl. *)
  (*          unfold Select_ap. simpl. reflexivity. *)
  (*      --- unfold Select_ap. *)
  (*          destruct z. *)
  (*          + simpl. *)
  destruct y.
  - destruct z.
    + simpl. unfold Select_ap. simpl.
      simpl.
      destruct x; simpl; reflexivity.
    + destruct z.
      * destruct s.
        -- 
        

Theorem select_selective_law3_assoc
  {A B C : Type} {F : Type -> Type} `{Functor F}
  (x : Select F (B + C))
  (y : Select F (A + (B -> C)))
  (z : Select F (A -> B -> C)) :
  x <*? (y <*? z) = (law3_f <$> x) <*? (law3_g <$> y) <*? (law3_h <$> z).
Proof.
  (* destruct y. *)
  (* - simpl. *)
  (*   destruct x. *)
  (*   + simpl. *)

  (* - destruct y. *)
  (*   + destruct s; *)
  (*     simpl; reflexivity. *)
  (*   + destruct s; *)
  (*     destruct z; *)
  (*     destruct s0; *)
  (*     simpl; reflexivity. *)
Admitted.

