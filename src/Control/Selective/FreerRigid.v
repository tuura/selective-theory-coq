Require Import Hask.Prelude.
Require Import Data.Either.
Require Import Data.Monoid.
Require Import Data.Functor.
Require Import Control.Applicative.
Require Import Control.Selective.
Require Import Coq.Strings.String.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Classes.Morphisms_Prop.
Require Import FunctionalExtensionality.
Require Import Omega.
From Equations Require Import Equations.

Inductive Select (F : Set -> Set) (A : Set) : Set :=
    Pure   : A -> Select F A
  | MkSelect : forall X : Set, Select F ((X -> A) + A) -> F X -> Select F A.

Arguments Pure {F} {A}.
Arguments MkSelect {F} {A} {X}.

(******************************************************************************)
(************************ Functor and FunctorLaws *****************************)
(******************************************************************************)
Equations(noind) Select_map {A B : Set} {F : Set -> Set}
           (f : A -> B) (x : Select F A) : Select F B :=
Select_map f (Pure a) => Pure (f a);
Select_map f (MkSelect x y) =>
  MkSelect (Select_map (Either_bimap (fun k : _ -> A => f ∘ k) f) x) y.

Instance Select_Functor (F : Set -> Set) : Functor (Select F) := {
  fmap := fun _ _ f x => Select_map f x
}.

Import FunctorLaws.

Program Instance Select_FunctorLaws : FunctorLaws (Select F).
(* Theorem Select_Functor_law1 {A : Set} *)
(*         `{Functor F} `{FunctorLaws F} : *)
(*   forall (x : Select F A), fmap id x = id x. *)
Obligation 1.
unfold id.
extensionality x.
generalize dependent x.
generalize dependent A.
induction x; simpl in *; trivial.
rewrite Select_map_equation_2.
f_equal.
assert (forall (A : Set), (fun x0 : A => x0) = id).
{ reflexivity. }
repeat rewrite H in *.
rewrite Either_bimap_id.
now rewrite IHx.
Qed.
(* Theorem Select_Functor_law2 {A B C : Set} *)
(*         `{Functor F} `{FunctorLaws F} : *)
(*   forall (f : B -> C) (g : A -> B) (x : Select F A), *)
(*   ((Select_map f) \o (Select_map g)) x = Select_map (f \o g) x. *)
Obligation 2.
extensionality x.
simpl.
revert B C f g.
induction x.
- trivial.
- intros b c f0 g.
  repeat rewrite Select_map_equation_2.
  f_equal.
  remember (Either_bimap (fun k : X -> b => f0 ∘ k) f0) as p.
  remember (Either_bimap (fun k : X -> A => g ∘ k) g) as q.
  remember (Either_bimap (fun k : X -> A => (f0 ∘ g) ∘ k) (f0 ∘ g)) as r.
  assert (p ∘ q = r).
  { extensionality y.
    simpl. rewrite Heqp. rewrite Heqq. rewrite Heqr.
    destruct y; trivial.
  }
  rewrite <- H.
  now rewrite IHx.
Qed.

(* This is a helper function used in the Select_selectBy definition *)
Definition g {A B C D E : Set}
           (f : A -> ((B -> C) + C))
           (a : A) :
  (((D -> B) + B) -> ((D -> C) + C)) + (E + C) :=
  match f a with
  | Right r => Right (Right r)
  | Left l => Left  (Either_bimap (comp l) l)
  end.

Equations(noind) Select_selectBy {A B C : Set} {F : Set -> Set}
          (f : A -> ((B -> C) + C))
          (x : Select F A)
          (a : Select F B) : Select F C :=
Select_selectBy f x (Pure y)       := (either (rev_f_ap y) id ∘ f) <$> x;
Select_selectBy f x (MkSelect y z) := MkSelect (Select_selectBy (g f) x y) z.

Definition Select_select {A B : Set} {F : Set -> Set}
           (x : Select F (A + B))
           (handler : Select F (A -> B)) : Select F B :=
  Select_selectBy (mapLeft rev_f_ap) x handler.


Definition Select_ap {A B : Set} {F : Set -> Set}
           (f : Select F (A -> B)) (x : Select F A) : Select F B :=
  Select_select (Left <$> f) (rev_f_ap <$> x).

Program Instance Select_Applicative
        (F : Set -> Set) : Applicative (Select F) :=
  { is_functor := Select_Functor F
  ; pure _ x := Pure x
  ; ap _ _ f x := Select_ap f x
}.

Program Instance Select_Selective
        (F : Set -> Set) : Selective (Select F) :=
  { is_applicative := Select_Applicative F
  ; select _ _ x f := Select_select x f
}.

Import ApplicativeLaws.

Program Instance Select_ApplicativeLaws : ApplicativeLaws (Select F).
Obligation 1.
Admitted.
Obligation 2.
Admitted.
Obligation 4.
Admitted.
Obligation 5.
Admitted.

(* Free theorems have to be declared as axioms *)

(* -- F1 (Free): f <$> select x y = select (fmap f <$> x) (fmap f <$> y) *)
(* f1 :: Selective f => (b -> c) -> f (Either a b) -> f (a -> b) -> f c *)
(* f1 f x y = f <$> select x y === select (fmap f <$> x) (fmap f <$> y) *)
Theorem Select_free_1 {F : Set -> Set} :
  forall (A B C : Set) (f : B -> C) (x : Select F (A + B)) (y : Select F (A -> B)),
    f <$> select x y = select (fmap f <$> x)
                              ((fun g : A -> B => f \o g) <$> y).
Admitted.

(* -- F2 (Free): select (first f <$> x) y = select x ((. f) <$> y) *)
(* f2 :: Selective f => (a -> c) -> f (Either a b) -> f (c -> b) -> f b *)
(* f2 f x y = select (first f <$> x) y === select x ((. f) <$> y) *)
Theorem Select_free_2 {F : Set -> Set} :
  forall (A B C : Set) (f : A -> C) (x : Select F (A + B)) (y : Select F (C -> B)),
    select (mapLeft f <$> x) y = select x ((fun g : C -> B => g \o f) <$> y).
Admitted.

(* -- F3 (Free): select x (f <$> y) = select (first (flip f) <$> x) (flip ($) <$> y) *)
(* f3 :: Selective f => (c -> a -> b) -> f (Either a b) -> f c -> f b *)
(* f3 f x y = select x (f <$> y) === select (first (flip f) <$> x) (flip ($) <$> y) *)
Theorem Select_free_3 {F : Set -> Set} :
  forall (A B C : Set) (f : C -> A -> B)
                        (x : Select F (A + B))
                        (y : Select F C),
    select x (f <$> y) = select (mapLeft (flip f) <$> x) (rev_f_ap <$> y).
Admitted.

Lemma Select_select_to_infix :
  forall (A B : Set) (F : Set -> Set)
  (x : Select F (A + B)%type) (y : Select F (A -> B)),
  Select_select x y = x <*? y.
Proof. reflexivity. Qed.

Lemma Select_map_to_fmap :
  forall (A B : Set) (F : Set -> Set)
  (x : Select F A) (f : A -> B),
  Select_map f x = fmap f x.
Proof. reflexivity. Qed.

(* p2 :: Selective f => a -> f (a -> b) -> f b *)
(* p2 x y = select (pure (Left  x)) y === y <*> pure x *)
(* This theorem can be proved for any rigid selective functor, i.e. if apS = (<*>) *)
Theorem Select_pure_left {F : Set -> Set} :
  forall (A B : Set) (x : A) (y : Select F (A -> B)),
    select (pure (Left x)) y = (rev_f_ap x) <$> y.
Proof.
  intros A B x y.
  (* The idea of the proof is to massage the goal into the form of the definition of Select_ap,
     fold the definition, substitute it with the applicative <*> and finish the prove using
     the Applicative laws. *)

  (* First, we use fmap_id to append an id application to the second argument of select *)
  assert ( select (Pure (inl x)) y =
           select (Pure (inl x)) (fmap id y)).
  { now rewrite fmap_id. }
  rewrite H. clear H.
  (* Now we use the third Selective Free Theorem to transfer the newly created id to the first argument
     of select and leave the second fmap'ed by the reverse function application *)
  rewrite Select_free_3.
  (* Drag the id inside Pure *)
  remember (fmap[ Select F] (mapLeft (flip id)) (Pure (inl x))) as p.
  compute in Heqp. simp Select_map in Heqp.
  rewrite Heqp. clear Heqp p.
  (* Use ap_homo to extract inl (aka Left) from Pure *)
  assert (Pure (inl (fun x0 : A -> B => x0 x)) <*? fmap[ Select F] rev_f_ap y =
          pure inl <*> Pure (fun x0 : A -> B => x0 x) <*? fmap[ Select F] rev_f_ap y).
  { now rewrite ap_homo. }
  rewrite H. clear H.
  (* Use ap_fmap to rewrite `pure inl <*>` as `inl <$>` *)
  assert (pure inl <*> Pure (fun x0 : A -> B => x0 x) <*? fmap[ Select F] rev_f_ap y =
          inl <$> Pure (fun x0 : A -> B => x0 x) <*? fmap[ Select F] rev_f_ap y).
  { now rewrite ap_fmap. }
  rewrite H. clear H.
  (* Fold reverse function application *)
  assert (inl <$> Pure (fun x0 : A -> B => x0 x) <*? fmap[ Select F] rev_f_ap y =
          inl <$> Pure (rev_f_ap x) <*? fmap[ Select F] rev_f_ap y).
  { reflexivity. }
  rewrite H. clear H.
  (* Unfold <*? to make the goal identical to Select_ap definition *)
  simpl "<*?".
  rewrite Select_map_to_fmap.
  remember (Pure (rev_f_ap x)) as g.
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

(* -- P1id (Identity): select x (pure id) == either id id <$> x *)
Theorem Select_Selective_law1 {F : Set -> Set} :
  forall (A B : Set) (x : Select F (A + B)) (y : A -> B),
    select x (Pure y) = either y id <$> x.
Proof.
  intros A B x y.
  simpl select.
  unfold Select_select.
  rewrite Select_selectBy_equation_1.
  f_equal.
  unfold comp.
  extensionality x0.
  destruct x0; trivial.
Qed.

Definition law3_f {A B C : Set}
           (x : B + C) : B + (A + C) := Right <$> x.

Definition law3_g {A B C : Set}
           (y : A + (B -> C)) : B -> A * B + C :=
  fun a => Either_bimap (fun p => pair p a) (rev_f_ap a) y.

Definition law3_h  {A B C : Set}
           (z : A -> B -> C) : A * B -> C := uncurry z.

Require Import Coq.Program.Equality.
Require Import Coq.Bool.Bool.

Lemma Select_law3_case_x_pure_left:
  forall (A B C : Set) (F : Set -> Set) (x : B)
    (y : Select F (A + (B -> C))) (z : Select F (A -> B -> C)),
    Pure (Left x) <*? (y <*? z) =
    (law3_f <$> (Pure (Left x))) <*? (law3_g <$> y) <*? (law3_h <$> z).
Proof.
  intros A B C F x y z.
  rewrite Select_pure_left.
  remember (fmap[ Select F] law3_f (Pure (inl x))) as p.
  simpl fmap in Heqp. simp Select_map in Heqp.
  rewrite Heqp. clear Heqp p.
  rewrite Select_pure_left.
  rewrite fmap_comp_x.
  rewrite Select_free_1.
  rewrite Select_free_3.
  remember (fmap[ Select F] (fun y0 : A + (B -> C) => rev_f_ap x (law3_g y0)) y <*? fmap[ Select F] law3_h z) as rhs.
  rewrite Select_free_3 in Heqrhs.
  rewrite Heqrhs. clear Heqrhs rhs.
  (* Now we can drop the subterm `<*? fmap[ Select F] rev_f_ap z`. *)
  f_equal.
  rewrite fmap_comp_x.
  rewrite fmap_comp_x.
  (* Drop the outher fmap *)
  f_equal.
  extensionality y0. destruct y0; trivial.
Qed.

Lemma Select_law3_case_x_pure_right:
  forall (A B C : Set) (F : Set -> Set) (x : C)
    (y : Select F (A + (B -> C))) (z : Select F (A -> B -> C)),
    Pure (Right x) <*? (y <*? z) =
    (law3_f <$> (Pure (Right x))) <*? (law3_g <$> y) <*? (law3_h <$> z).
Proof.
  intros A B C F x y z.
  remember (fmap[ Select F] law3_f (Pure (inr x))) as p.
  simpl fmap in Heqp. simp Select_map in Heqp.
  unfold law3_f in Heqp. simpl fmap in Heqp.
  rewrite Heqp. clear Heqp p.
  remember (Pure (inr (inr x)) <*? fmap[ Select F] law3_g y <*? fmap[ Select F] law3_h z) as rhs.
  rewrite Select_free_3 in Heqrhs.
  rewrite Select_free_1 in Heqrhs.
  rewrite fmap_comp_x in Heqrhs.
  remember (fmap[ Select F] (fmap[ sum B] (mapLeft (flip law3_h))) (Pure (inr (inr x)))) as p.
  simpl fmap in Heqp. simp Select_map in Heqp. simpl Either_map in Heqp.
  rewrite Heqp in Heqrhs. clear Heqp p.
  remember (Pure (inr (inr x)) <*? fmap[ Select F] (fun y : A + (B -> C) => mapLeft (flip law3_h) \o law3_g y) y) as p.
  rewrite Select_free_3 in Heqp.
  rewrite Heqp in Heqrhs. clear Heqp p.
  remember (fmap[ Select F] (mapLeft (flip (fun y : A + (B -> C) => mapLeft (flip law3_h) \o law3_g y)))
                (Pure (inr (inr x)))) as p.
  simpl fmap in Heqp. simp Select_map in Heqp. simpl mapLeft in Heqp.
  rewrite Heqp in Heqrhs. clear Heqp p.
  remember ( Pure (inr (inr x)) <*? fmap[ Select F] law3_g y) as p.
  rewrite Select_free_3 in Heqp.
  remember (fmap[ Select F] (mapLeft (flip law3_g)) (Pure (inr (inr x)))) as q.
  simpl fmap in Heqq. simp Select_map in Heqq. simpl mapLeft in Heqq.
  rewrite Heqrhs. clear Heqrhs rhs Heqp p Heqq q.
  dependent induction z.
  - remember (fmap[ Select F] rev_f_ap (Pure a)) as q.
    simpl fmap in Heqq. simp Select_map in Heqq. rewrite Heqq. clear Heqq q.
    remember (Pure (inr (inr x)) <*? fmap[ Select F] rev_f_ap y <*? Pure (rev_f_ap a)) as rhs.
    remember (Pure (inr (inr x)) <*? fmap[ Select F] rev_f_ap y) as p.
    rewrite Select_Selective_law1 in Heqrhs.
    rewrite Heqp in Heqrhs. clear Heqp p.
    rewrite Heqrhs. clear Heqrhs rhs.
    remember (y <*? Pure a) as p.
    simpl "<*?" in Heqp. unfold Select_select in Heqp. simp Select_selectBy in Heqp.
    rewrite Heqp. clear Heqp p.
    remember (fmap[ Select F] (either (rev_f_ap a) id) (Pure (inr (inr x)) <*? fmap[ Select F] rev_f_ap y)) as p.
    rewrite Select_free_1 in Heqp.
    rewrite fmap_comp_x in Heqp.
    rewrite Heqp. clear Heqp p.
    remember (fmap[ Select F] (fmap[ sum (A + (B -> C) -> ((A -> B -> C) -> C) + C)] (either (rev_f_ap a) id))
                  (Pure (inr (inr x)))) as p.
    simpl fmap in Heqp. simp Select_map in Heqp. simpl Either_map in Heqp. unfold id in Heqp.
    rewrite Heqp. clear Heqp p.
    remember (Pure (inr x) <*? fmap[ Select F] (either (rev_f_ap a) id \o mapLeft rev_f_ap) y) as lhs.
    remember (Pure (inr x) <*? fmap[ Select F] (fun y0 : A + (B -> C) => either (rev_f_ap a) id \o rev_f_ap y0) y) as rhs.
    rewrite Select_free_3 in Heqlhs.
    rewrite Select_free_3 in Heqrhs.
    simpl fmap in Heqlhs. simp Select_map in Heqlhs. simpl mapLeft in Heqlhs.
    simpl fmap in Heqrhs. simp Select_map in Heqrhs. simpl mapLeft in Heqrhs.
    rewrite Heqlhs. rewrite Heqrhs. reflexivity.
  - (* transform lhs by evaluating select two times *)
    remember (y <*? MkSelect z f) as p.
    simpl "<*?" in Heqp. unfold Select_select in Heqp.
    simp Select_selectBy in Heqp.
    rewrite Heqp. clear Heqp p.
    remember (Pure (inr x) <*? MkSelect (Select_selectBy (g (mapLeft rev_f_ap)) y z) f) as p.
    simpl "<*?" in Heqp. unfold Select_select in Heqp.
    simp Select_selectBy in Heqp.
    rewrite Heqp. clear Heqp p.
    (* now tranform rhs... *)
    remember (Pure (inr (inr x)) <*? fmap[ Select F] rev_f_ap y <*? fmap[ Select F] rev_f_ap (MkSelect z f)) as p.
    remember ( Pure (inr (inr x)) <*? fmap[ Select F] rev_f_ap y) as q.
    simpl "<*?" in Heqp. unfold Select_select in Heqp.
    simp Select_map in Heqp.
    simp Select_selectBy in Heqp.
    rewrite Heqq in Heqp. clear Heqq q.
    rewrite Heqp. clear Heqp p.
    f_equal.
    rewrite Select_map_to_fmap.
    assert (g (mapLeft rev_f_ap) = mapLeft rev_f_ap).
    rewrite IHz.
    remember ((fmap[ Select F] (Either_bimap (fun k : X -> A -> B -> C => rev_f_ap \o k) rev_f_ap) z)) as p.
    unfold comp in Heqp. unfold rev_f_ap in Heqp.


Admitted.

Theorem Select_Selective_law3_assoc :
  forall (A B C : Set) (F : Set -> Set)
  (x : Select F (B + C))
  (y : Select F (A + (B -> C)))
  (z : Select F (A -> B -> C)),
  x <*? (y <*? z) = (law3_f <$> x) <*? (law3_g <$> y) <*? (law3_h <$> z).
Proof.
  (* dependent induction y. *)
  (* -  *)

  (* dependent induction z. *)
  (* - remember (y <*? Pure a) as p. *)
  (*   simpl "<*?" in Heqp. *)
  (*   unfold Select_select in Heqp. *)
  (*   rewrite Select_selectBy_equation_1 in Heqp. *)
  (*   rewrite Heqp. clear Heqp p. *)
  (*   remember (fmap[ Select F] law3_g y <*? fmap[ Select F] law3_h (Pure a)) as p. *)
Admitted.

(* This is a proof of the (Pure Right) case of the distributivity theorem for rigid
   selective functors. Assumes the associativity law. *)
Lemma Select_Selective_law2_case_right {F : Set -> Set} {H: ApplicativeLaws (Select F)} :
  forall (A B : Set) (x : B) (y : Select F (A -> B)) (z : Select F (A -> B)),
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
  simpl in Heqp. simp Select_map in Heqp. simpl Either_map in Heqp.
  rewrite Heqp in Heqrhs. clear Heqp p.
  remember (fmap[ Select F] law3_f
             (fmap[ Select F] (fmap[ sum A] (fun y0 : B => inl (const id y0)))
                (Pure (inr x)) <*?
         fmap[ Select F] (fun g : A -> B => (fun y0 : B => inl (const id y0)) \o g) y)) as p.
  assert (p <*? Pure (law3_g (inr (rev_f_ap x))) =
          either (law3_g (inr (rev_f_ap x))) id <$> p).
  { now rewrite Select_Selective_law1. }
  rewrite H0 in Heqrhs. clear H0.
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
  compute in Heqp. simp Select_map in Heqp. rewrite Heqp in Heqrhs. clear Heqp p.
  remember (fmap[ Select F] law3_f (Pure (inr x))) as p.
  compute in Heqp. simp Select_map in Heqp. rewrite Heqp in Heqlhs. clear Heqp p.
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
Qed.

(* -- D1 (distributivity): pure x <*? (y *> z) = (pure x <*? y) *> (pure x <*? z) *)
(* d1 :: Selective f => Either a b -> f (a -> b) -> f (a -> b) -> f b *)
(* NB:  This law appers to be a 'theorem' if we only consider rigid selective functos. *)
(* NB2: The following proof assumes 'pure-left' and the associativity law (law 3) *)
Theorem Select_Selective_law2 {F : Set -> Set} {H: ApplicativeLaws (Select F)} :
  forall (A B : Set) (x : A + B) (y : Select F (A -> B)) (z : Select F (A -> B)),
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
  - apply Select_Selective_law2_case_right.
Qed.

(* To prove applicative laws we, again, must (?) assume pure-left *)
Theorem Select_Applicative_law1 {F : Set -> Set} :
  forall (A : Set),
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
