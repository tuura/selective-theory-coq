Require Import Reasoning.
Require Import Hask.Prelude.
Require Import Data.Functor.
Require Import Data.Either.
Require Import Control.Applicative.
Require Import Control.Selective.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Equations.Equations.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

Inductive Select (F : Set -> Set) (A : Set) : Set:=
    Pure   : A -> Select F A
  | MkSelect : forall B, Select F (B + A) -> F (B -> A) -> Select F A.

Arguments Pure {F} {A}.
Arguments MkSelect {F} {A} {B}.

Section WithF.
  Context {F : Set -> Set}.
  Context {HF : Functor F}.

  Equations(noind) Select_map {A B : Set}
             (f : A -> B) (x : Select F A) : Select F B :=
  Select_map f (Pure a)       => Pure (f a);
  Select_map f (MkSelect x y) => MkSelect (Select_map (fmap[Either _] f) x)
                                         (fmap       (fmap[→_]       f) y).

  Equations(noind) Select_depth {A : Set}
           (x : Select F A) : nat :=
  Select_depth (Pure a)       := O;
  Select_depth (MkSelect y _) := S (Select_depth y).

  Lemma Select_depth_pure :
    forall (A : Set) (x : Select F A) (H : Select_depth x = O), (exists a, x = Pure a).
  Proof.
    intros.
    destruct x.
    - now exists a.
    - simp Select_depth in H. discriminate H.
  Qed.

  Lemma Select_depth_MkSelect :
    forall (A : Set)
      (x : Select F A) (n : nat) (HGt : Select_depth x = S n),
      (exists (B : Set) (y : Select F (B + A)) (z : F (B -> A)), x = MkSelect y z).
  Proof.
    intros A x n HGt.
    destruct x.
    - simp Select_depth in HGt. discriminate.
    - exists B. exists x. now exists f.
  Qed.

  Lemma Select_fmap_preserves_depth {A B : Set} :
    forall (x : Select F A) (f : A -> B),
    Select_depth (Select_map f x) = Select_depth x.
  Proof.
    intros x.
    revert B.
    induction x as [| A b s IH handler]; trivial; simpl in *; intros f1 B.
    - repeat rewrite Select_map_equation_2. simp Select_depth. now rewrite IH.
  Qed.

  (***************************************************************)
  Global Instance Select_Functor : Functor (Select F) := {
    fmap := fun _ _ f x => Select_map f x
  }.

Definition law3_f {A B C : Set}
           (x : B + C) : B + (A + C) := Right <$> x.

Lemma law3_f_cancel :
  forall (A B C : Set),
  (@law3_f A _ _) ∘ (@Left B C) = Left.
Proof. intros. extensionality x. now cbn. Qed.

Definition law3_g {A B C : Set}
           (y : A + (B -> C)) : B -> A * B + C :=
  fun a => Either_bimap (fun p => pair p a) (fun f => f a) y.

Definition law3_h  {A B C : Set}
           (f : A -> B -> C) : A * B -> C := uncurry f.

Equations(noind) Select_select {A B : Set}
          (x : Select F (A + B)) (handler : Select F (A -> B))
  : (Select F B) by wf (Select_depth handler) lt :=
Select_select x (Pure y) := fmap[Select F] (either y id) x;
Select_select x (MkSelect y z) :=
  MkSelect (Select_select (fmap[Select F] law3_f x) (fmap[Select F] law3_g y))
           (fmap[F] law3_h z).
Next Obligation.
Proof.
cbn.
rewrite Select_fmap_preserves_depth.
simp Select_depth.
Defined.

Definition Select_ap {A B : Set}
           (f : Select F (A -> B)) (x : Select F A) : Select F B :=
  Select_select (Left <$> f) (rev_f_ap <$> x).

(***************************************************************)
Global Instance Select_Applicative : Applicative (Select F) := {
  pure _ x := Pure x;
  ap _ _ f x  := Select_ap f x
}.

(***************************************************************)
Global Instance Select_Selective : Selective (Select F) := {
  select _ _ x f := Select_select x f
}.

(***************************************************************)
(***************************************************************)
(***************************************************************)

(* (* O(n) select implementation *) *)
Fixpoint Select_select_go {A B C : Set}
         (x : Select F (A + B)) (s : Select F C) (k : C -> (A -> B)) {struct s} :
         Select F B :=
  match s with
  | Pure y => either (k y) id <$> x
  | MkSelect y z =>
    MkSelect (Select_select_go (law3_f <$> x)
                               y
                               (law3_g ∘ (fmap[Either _] k))
             )
             ((law3_h ∘ (fmap[→_] k)) <$> z)
  end.

Fixpoint Select_select'  {A B : Set}
         (x : Select F (B + A)) (f : Select F (B -> A)) : Select F A :=
  Select_select_go x f id.

End WithF.
