Require Import Coq.Program.Basics.
Require Import Hask.Prelude.
Require Import Data.Either.
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

(* Free Selective functor construction *)
Inductive Select (F : Type -> Type) (a : Type) :=
    Pure     : a -> Select F a
  | MkSelect {b : Type} : Select F (b + a) -> F (b -> a) -> Select F a.

Arguments Pure {F} {a}.
Arguments MkSelect {F} {a} {b}.

(* Note that `fmap` for `Select` implementation uses two `Functor` instances in its
   implemetation:
     Either for the first argument of the `MkSelect` constructor and
     Function for the second.
   Here we avoid using the instances and instead use the appropriate `fmap`
   implementations explicitely: `Either_map` and function composition
*)
Fixpoint Select_map {A B : Type} `{Functor F}
           (f : A -> B) (x : Select F A) : Select F B :=
  match x with
  | Pure a => Pure (f a)
  | @MkSelect _ _ b x y => MkSelect (Select_map (Either_map f) x)
                                    ((fun k : b -> A => f \o k) <$> y)
  end.

(* We will need use the depth of the `Select` values as measure for defining
   non-structuraly recursive functions. *)
Fixpoint Select_depth {A : Type} `{Functor F}
         (x : Select F A) : nat :=
  match x with
  | Pure a   => O
  | MkSelect y _ => S (Select_depth y)
  end.

(* Troubles starts here! *)
(* We would like now to prove theorems involving `Select` and will need to use
   its associated induction principle. We start from the fact that the `Select_map`
   must not change the depth of the expression. *)
Lemma Select_fmap_preserves_depth {A B : Type} `{Functor F} :
  forall (x : Select F A) (f : A -> B),
  Select_depth (Select_map f x) = Select_depth x.
Proof.
  (* We perform the induction on the free selective construction*)
  induction x as [| A b s IH handler]; simpl in *; intros f1.
  - (* The `Pure` case is discharged trivially *)
    reflexivity.
  - (* The proof of the `MkSelect` starts from applying the `f_equal` tactic to get rid
       of the `MkSelect` constructor. *)
    f_equal.
    (* and now the goal appears to be unprovable: *)
  (* B : Type *)
  (* F : Type -> Type *)
  (* H : Functor F *)
  (* a : Type *)
  (* b : Type *)
  (* s : Select F (b + A) *)
  (* selector : F (b -> A) *)
  (* IH : forall f : b + A -> B, Select_depth (Select_map f s) = Select_depth s *)
  (* f1 : A -> B *)
  (* ============================ *)
  (* Select_depth (Select_map (Either_map f1) s) = Select_depth s *)

    (* The problematic thing is the parameter of the inductive hypothesis `f : b + A -> B`,
       which is impossible to construct from the entities we have in the context.
       It feels more intuitive that `IH` should instead have been parametrised by a function
       of type `b + A -> b + B`, because then we would have been able to give it
       `Either_map f1` and then apply IH directly and solve the goal.
       
       The question is: is there anything to do here? Should I somehow modify the
       inductive principle `Select_ind`? Or maybe I'm doing some of the bookkeeping in the
       proof wrong and rendering the goal unprovable?


     *)
Admitted.

(* Interestengly, if we limit the function `f` to be the identity by restricting
   its type to be `A -> A`*)
Lemma Select_fmap_id_preserves_depth {A : Type} `{Functor F} :
  forall (x : Select F A) (f : A -> A),
  Select_depth (Select_map f x) = Select_depth x.
Proof.
  induction x as [| A b s IH handler]; simpl in *; intros f1.
    reflexivity.
    f_equal.
    (* Now the inductive hypothesis is parametrised by `f : b + A -> b + A`, since
       parametricity has forced Coq to preserve `+`. How do I force Coq to preserve
       this information in the `A -> B` case? *) 
    apply (IH (Either_map f1)).
Qed.

(* The depth preesrvation theorem is a very simple one, but still I can't find a way to
   prove it. If I developed the required technique, I would also want to prove the
   Functor composition law: *)

Lemma fmap_rewrite_compose {A B C : Type} `{Functor F} :
  forall (f : B -> C) (g : A -> B) (x : F A), 
    fmap f (fmap g x) = (fmap f \o fmap g) x.
Proof.
  intros f g x.
  reflexivity.
Qed.

Import FunctorLaws.
Theorem Select_Functor_law2
        `{Functor F} `{FunctorLaws F} :
  forall {A B C : Type} (g : A -> B) (f : B -> C),
    ((Select_map f) \o (Select_map g)) = Select_map (f \o g).
Proof.
  intros A B C g f.
  extensionality x.
  simpl.
  induction x as [| A b s IH selector]; simpl in *.
  - reflexivity.
  - f_equal.
    + (* The first goal appears to be unprovable due to the same issue that arose in
         the `Select_map_reserves_depth` theorem *)
      admit.
    + (* The second subgoal here is discharged by Functor laws for functions *)
      rewrite fmap_rewrite_compose.
      rewrite fmap_comp.
      f_equal.
Admitted.

