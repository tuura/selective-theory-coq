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

(* Note that `fmap` for `Select` implementation uses two `Functor` instances in its
   implemetation:
     Either for the first argument of the `MkSelect` constructor and
     Function for the second.
   Here we avoid using the instances and instead use the appropriate `fmap`
   implementations explicitely: `Either_map` and function composition
*)
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
induction x as [| A b s IH handler]; trivial; simpl in *.
- f_equal.
  * rewrite Either_map_id.
    apply IH.
  * setoid_rewrite compose_id. (* rewrite under the fun binder *)
    now rewrite fmap_id.
Qed.
(* Theorem Select_Functor_law2 {A B C : Type} *)
(*         `{Functor F} `{FunctorLaws F} : *)
(*   forall (f : B -> C) (g : A -> B) (x : Select F A), *)
(*   ((Select_map f) \o (Select_map g)) x = Select_map (f \o g) x. *)
Obligation 2.
extensionality x.
simpl.
(* It is SUPER IMPORTANT to generalise the two type variables B and C
   (and thus also the functions f and g), because otherwise the
   inductive hypothesis will be not general enough! *)
revert b c g f.
induction x as [| A b s IH selector]; simpl in *; trivial; intros B C g f.
- f_equal.
  + (* Let us explicitely specify all parameters of the IH, note that
       B is instantiated as (b + B) and C as (c + C) *)
    rewrite (IH (b + B)%type (b + C)%type (Either_map g) (Either_map f)).
    now rewrite Either_map_comp.
  + (* The second subgoal here is discharged by Functor laws for functions *)
    rewrite fmap_rewrite_compose.
    now rewrite fmap_comp.
Qed.
    
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

