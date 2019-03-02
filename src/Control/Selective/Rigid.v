Require Import Coq.Program.Basics.
Require Import Hask.Prelude.
Require Import Data.Either.
Require Import Data.Monoid.
Require Import Data.Functor.
Require Import Control.Applicative.
Require Import Control.Selective.
(* Require Import Data.Over. *)
Require Import Coq.Strings.String.


Inductive Select (f : Type -> Type) (a : Type) :=
    Pure   : a -> Select f a
  | MkSelect : forall b, Select f (Either b a) -> f (b -> a) -> Select f a.

Arguments Pure {f} {a}.
Arguments MkSelect {f} {a} {b}.

Fixpoint Select_map {A B : Type} {F : Type -> Type} `{Functor F}
           (f : (B -> A)) (x : Select F B) : Select F A :=
  match x with
  | Pure a => Pure (f a)
  | MkSelect x y => MkSelect (Select_map (fmap f) x) ((fun g => compose f g) <$> y)
  end.

Program Instance Select_Functor (F : Type -> Type)
  `{Functor F} : Functor (Select F) := {
  fmap := fun _ _ f x => Select_map f x
}.

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
(* ?O(n)? select implementation *) 
Fixpoint Select_select_go {A B C : Type} {F : Type -> Type} `{Functor F}
         (x : Select F (A + B)) (s : Select F C) (k : C -> (A -> B)) : Select F B :=
  match s with
  | Pure y => either (k y) id <$> x
  | MkSelect y z =>
    MkSelect (Select_select_go (law3_f <$> x)
                               y
                               (compose law3_g (mapRight k))
             )
             (compose law3_h (compose k) <$> z)
  end.

Fixpoint Select_select  {A B : Type} {F : Type -> Type} `{Functor F}
         (x : Select F (B + A)) (f : Select F (B -> A)) {struct f} : Select F A :=
  Select_select_go x f id.

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
        -- simpl. unfold Select_ap.

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

