Require Import Hask.Prelude.
Require Import Reasoning.
Require Import Data.Functor.
Require Import Data.Either.
Require Import Control.Applicative.
Require Import Control.Selective.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Equations.Equations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Hask.Control.Selective.Rigid.
Require Import Hask.Control.Selective.Rigid.Parametricity.
Require Import Hask.Control.Selective.Rigid.Proofs.Functor.

Section Select_ApplicativeLaws_Proofs.

Import FunctorLaws.
Import ApplicativeLaws.
(* Import SelectiveParametricity. *)

Context (F : Set -> Set).
Context (FFunctor : Functor F).
Context (FFunctorLaws : FunctorLaws F).

Lemma boring_details :
  forall (A B X : Set) (g : A -> X),
  ((Either_bimap (fun (y : B) (h : B -> A) => g (h y)) g) = (
    ((flip ((fmap[→_] ((mapLeft (flip (law3_h ∘ fmap[→B] rev_f_ap))))) ∘
      law3_g ∘ fmap[ Either B] rev_f_ap))) g)).
Proof. intros. extensionality z; now destruct z. Qed.

Lemma boring_details_2:
      forall (A B : Set)
        (X : Set) (g : A -> X),
          (Either_bimap (fun y h  => g (h y)) g) =
          (flip ((fun g0  => (mapLeft (flip (fun g1 : B -> A => g ∘ g1))) ∘ g0) ∘ rev_f_ap)
                (mapRight g)).
Proof. intros A B X g. extensionality x. now destruct x. Qed.

Lemma ap_fmap_selectors_equal :
  forall (A B : Set) (x : Select F (B + A)) (f : F (B -> A)) (X : Set) (g : A -> X),
  mapLeft (flip (fmap[→B] g)) <$>
      (select (fmap[ Select F] Left ((pure[ Select F]) (fmap[ Either B] g)))
              (fmap[ Select F] rev_f_ap x)) =
  mapLeft (flip (law3_h ∘ fmap[→B] rev_f_ap)) <$>
      (select (fmap[ Select F] (law3_f ∘ Left) ((pure[ Select F]) g))
              (fmap[ Select F] (law3_g ∘ fmap[ Either B] rev_f_ap) x)).
Proof.
  intros A B x f X g.
`Begin
    (mapLeft (flip (fmap[→B] g)) <$>
        (select (fmap Left ((pure (fmap[ Either B] g))))
                (fmap[ Select F] rev_f_ap x))).
  ≡⟨ reflexivity ⟩
    (mapLeft (flip (fmap[→B] g)) <$>
        (select (pure (Left (fmap[Either B] g)))
                (fmap[ Select F] rev_f_ap x))).
  ≡⟨ now rewrite <- free_theorem_1 ⟩
       (select ((fmap[Either _] (mapLeft (flip (fmap[ → (B)] g)))) <$>
                    (pure[Select F] (Left (fmap[Either B] g))))
               ((fmap[→_] (mapLeft (flip (fmap[ → (B)] g)))) <$>
                    (fmap[ Select F] rev_f_ap x))).
  ≡⟨ reflexivity ⟩
       (select (pure[Select F] (Left (fmap[Either B] g)))
               ((fmap[→_] (mapLeft (flip (fmap[ → (B)] g)))) <$>
                    (fmap[ Select F] rev_f_ap x))).
  ≡⟨ reflexivity ⟩
       (select (pure[Select F] (Left (fmap[Either B] g)))
               ((fmap[→_] (mapLeft (flip (fmap[ → (B)] g)))) <$>
                    (rev_f_ap <$> x))).
  ≡⟨ now setoid_rewrite fmap_comp_x ⟩
       (select (pure[Select F] (Left (fmap[Either B] g)))
               ((((fmap[→_] (mapLeft (flip (fmap[ → (B)] g)))) ∘ rev_f_ap) <$> x))).
  ≡⟨ now setoid_rewrite <- free_theorem_3 ⟩
       (select ((mapLeft (flip
     (((fmap[→_] (mapLeft (flip (fmap[ → (B)] g)))) ∘ rev_f_ap)))) <$>
                 pure[Select F] (Left (fmap[Either B] g)))
               (rev_f_ap <$> x)).
  ≡⟨ specialize (boring_details_2);
    intros L;
    cbv in *; simp Select_map;
    now rewrite <- L ⟩
       (select (pure (Left (Either_bimap (fun (y : B) (h : B -> A) => g (h y)) g)))
               (rev_f_ap <$> x)).
  ≡⟨ now rewrite boring_details ⟩
       (select ((pure (Left (
           ((flip ((fmap[→_] ((mapLeft (flip (law3_h ∘ fmap[→B] rev_f_ap))))) ∘
           law3_g ∘ fmap[ Either B] rev_f_ap))) g))) )
               (rev_f_ap <$> x)).
  ≡⟨ reflexivity ⟩
       (select ((mapLeft (flip ((fmap[→_] ((mapLeft (flip (law3_h ∘ fmap[→B] rev_f_ap))))) ∘
                 law3_g ∘ fmap[ Either B] rev_f_ap))) <$>
                (pure[ Select F] (Left g)) )
               (rev_f_ap <$> x)).
  ≡⟨ now setoid_rewrite <- free_theorem_3 ⟩
       (select ((pure[ Select F]) (Left g))
               ((((fmap[→_] ((mapLeft (flip (law3_h ∘ fmap[→B] rev_f_ap))))) ∘
                  law3_g ∘ fmap[ Either B] rev_f_ap) <$> x))).
  ≡⟨ reflexivity ⟩
       (select ((fmap[ Select F]
                     ((fmap[Either _] ((mapLeft (flip (law3_h ∘ fmap[→B] rev_f_ap))))) ∘
                     (fmap Right) ∘ Left) ((pure[ Select F]) g)))
               ((((fmap[→_] ((mapLeft (flip (law3_h ∘ fmap[→B] rev_f_ap))))) ∘
                  law3_g ∘ fmap[ Either B] rev_f_ap) <$> x))).
  ≡⟨ unfold law3_f; now repeat rewrite fmap_comp_x ⟩
       (select (fmap[Either _] ((mapLeft (flip (law3_h ∘ fmap[→B] rev_f_ap)))) <$>
                    (fmap[ Select F] (law3_f ∘ Left) ((pure[ Select F]) g)))
               (fmap[→_] ((mapLeft (flip (law3_h ∘ fmap[→B] rev_f_ap)))) <$>
                    (fmap[ Select F] (law3_g ∘ fmap[ Either B] rev_f_ap) x))).
  ≡⟨ now rewrite <- free_theorem_1 ⟩
       ((mapLeft (flip (law3_h ∘ fmap[→B] rev_f_ap))) <$>
    select (fmap[ Select F] (law3_f ∘ Left) ((pure[ Select F]) g))
           (fmap[ Select F] (law3_g ∘ fmap[ Either B] rev_f_ap) x))
  `End.
Qed.

Theorem Select_ap_fmap :
  forall (A B : Set) (x : Select F A) (f : A -> B),
  pure[Select F] f <*> x = fmap f x.
Proof.
  intros A B x f.
  generalize dependent B.
  generalize dependent A.
  induction x; trivial.
  - intros X g.
    specialize (IHx (B + X)%type (fmap[Either B] g)).
    `Begin
     (pure g <*> (MkSelect x f)).
    ≡⟨ reflexivity ⟩
     (select (fmap[ Select F] Left (Pure g))
             (fmap[ Select F] rev_f_ap (MkSelect x f))).
    ≡⟨ reflexivity ⟩
     (select (fmap[ Select F] Left (Pure g))
             (MkSelect (fmap (fmap[ Either B] rev_f_ap) x)
                       (fmap[ F] (fmap[→B] rev_f_ap) f))).
    ≡⟨ simpl select; now simp Select_select ⟩
     (MkSelect
       (select (fmap[ Select F] law3_f (fmap Left (pure g)))
               (fmap[ Select F] law3_g (fmap[Select F] (fmap rev_f_ap) x)))
       (fmap[ F] law3_h (fmap[ F] (fmap[→B] rev_f_ap) f))).
    ≡⟨ now repeat rewrite <- fmap_comp ⟩
    (MkSelect
       (select (fmap (law3_f ∘ Left) (pure g))
               (fmap (law3_g ∘ (fmap rev_f_ap)) x))
       (fmap (law3_h ∘ (fmap[→B] rev_f_ap)) f)).
    ≡⟨ now setoid_rewrite <- free_theorem_3_MkSelect ⟩
    (MkSelect
       (mapLeft (flip (law3_h ∘ (fmap[→B] rev_f_ap))) <$>
          (select (fmap (law3_f ∘ Left) (pure g))
                  (fmap (law3_g ∘ (fmap rev_f_ap)) x)))
       (fmap rev_f_ap f)).
    ≡⟨ now rewrite ap_fmap_selectors_equal ⟩
     (MkSelect
        (mapLeft (flip (fmap[→B] g)) <$>
           (select (fmap Left (pure (fmap[Either B] g)))
                   (fmap rev_f_ap x)))
        (fmap rev_f_ap f)).
    ≡⟨ now setoid_rewrite <- free_theorem_3_MkSelect ⟩
     (MkSelect
        (select (fmap Left (pure (fmap[Either B] g)))
                (fmap rev_f_ap x))
        ((fmap[→B] g) <$> f)).
    ≡⟨ reflexivity ⟩
     (MkSelect (pure (fmap[Either B] g) <*> x) ((fmap[→B] g) <$> f)).
    ≡⟨ now setoid_rewrite IHx ⟩
     (MkSelect ((fmap[Either B] g) <$> x) ((fmap[→B] g) <$> f)).
    ≡⟨ reflexivity ⟩
     (fmap g (MkSelect x f))
    `End.
Qed.

Theorem Select_ApplicativeLaws_interchange :
  forall (A B : Set) (u : Select F (A -> B)) (y : A),
  u <*> pure y = pure (rev_f_ap y) <*> u.
Proof.
  intros A B u y.
  destruct u as [ f | X v g ] .
  -`Begin
    (pure[Select F] f <*> pure y).
   ≡⟨ reflexivity ⟩
    (Select_ap (Pure f) (pure y)).
   ≡⟨ reflexivity ⟩
    (select (Left <$> pure f) (rev_f_ap <$> pure y)).
   ≡⟨ reflexivity ⟩
    (select (Left <$> pure f) (pure (rev_f_ap y))).
   ≡⟨ reflexivity ⟩
    (select (Left <$> pure f) (pure (rev_f_ap y))).
   ≡⟨ now rewrite <- Select_select_equation_1 ⟩
    ((either (rev_f_ap y) (@id _)) <$> (pure[Select F] (Left f))).
   ≡⟨ reflexivity ⟩
    (pure[Select F] (rev_f_ap y f)).
   ≡⟨ functor_laws ⟩
    (rev_f_ap y <$> (pure[Select F] f)).
   ≡⟨ now rewrite Select_ap_fmap ⟩
    (pure[Select F] (rev_f_ap y) <*> pure f)
   `End.
  -`Begin
    (MkSelect v g <*> pure y).
   ≡⟨ reflexivity ⟩
    (Select_ap (MkSelect v g) (pure y)).
   ≡⟨ reflexivity ⟩
    (select (Left <$> (MkSelect v g)) (rev_f_ap <$> pure y)).
   ≡⟨ reflexivity ⟩
    (select (Left <$> (MkSelect v g)) (pure (rev_f_ap y))).
   ≡⟨ now rewrite <- Select_select_equation_1 ⟩
    ((either (rev_f_ap y) id) <$> (Left <$> (MkSelect v g))).
   ≡⟨ now rewrite <- fmap_comp ⟩
    (((either (rev_f_ap y) id) ∘ Left) <$> (MkSelect v g)).
   ≡⟨ trivial ⟩
    (rev_f_ap y <$> MkSelect v g).
   ≡⟨ now rewrite Select_ap_fmap ⟩
    (pure (rev_f_ap y) <*> (MkSelect v g))
  `End.
Qed.

Lemma boring_details_3:
  forall (A : Set) (a : A) (B : Set),
    Select F (A -> B) ->
    forall (C : Set) (u : Select F (B -> C)),
      (mapLeft (B := C) (flip (rev_f_ap ∘ rev_f_ap a))) <$> (Left <$> u) =
      (mapLeft (flip (comp (rev_f_ap a) ∘ rev_f_ap))) <$> (Left <$> (comp <$> u)).
Proof.
  intros A a B v C u.
  repeat rewrite fmap_comp_x.
  f_equal.
Qed.

Lemma mapLeft_drag_into_left : forall (A B X: Set) (F : Set -> Set) (H : Functor F)
                                 (f : A -> B) (x : F A),
    (mapLeft f ∘ (@Left A X)) <$> x = (Left ∘ f) <$> x.
Proof. intros. f_equal. Qed.

Lemma ap_comp_boring_details :
  forall (A B X C : Set)
    (w : Select F (B + A)) (v : Select F (A -> X)) (u : Select F (X -> C))
    z'' (Heqz'' : z'' =
           flip
             (fmap[ → ((A -> X) -> B + A -> B * (A -> C) + C)]
                (flip
                   (fmap[ → (B + A -> B * (A -> C) + C)]
                      (mapLeft (flip (law3_h ∘ fmap[ → (B)] rev_f_ap))) ∘ rev_f_ap)) ∘
              rev_f_ap) ∘
           (fun (f : X -> C) (g : A -> X) => Either_bimap (flip pair (f ∘ g)) (f ∘ g)))
    t (Heqt : t =
         (fun y : B + A =>
          fmap[ → (A -> X)]
            (fmap[ → (X -> C)]
               (mapLeft
                  (flip
                     (((law3_h ∘ fmap[ → (B * (A -> X))] rev_f_ap) ∘ law3_h) ∘
                      fmap[ → (B)] rev_f_ap))))
            ((((fmap[ → (A -> X)] law3_g ∘
                fmap[ → (A -> X)] (fmap[ Either (B * (A -> X))] rev_f_ap)) ∘ law3_g) ∘
              fmap[ Either B] rev_f_ap) y))),
      fmap comp (fmap[ Select F] rev_f_ap u) <*> fmap[ Select F] (flip t) v <*> w =
      fmap z'' u <*> v <*> w.
Proof.
  intros A B X C w v u z'' Heqz'' t Heqt.
    f_equal.
  `Begin
  (fmap[ Select F] comp (fmap[ Select F] rev_f_ap u) <*> fmap[ Select F] (flip t) v).
  ≡⟨ reflexivity ⟩
  (select (Left <$> (fmap[ Select F] comp (fmap[ Select F] rev_f_ap u)))
          (rev_f_ap <$> (fmap[ Select F] (flip t) v))).
  ≡⟨ functor_laws ⟩
  (select (Left <$> (fmap[ Select F] comp (fmap[ Select F] rev_f_ap u)))
          ((rev_f_ap ∘ flip t) <$> v)).
  ≡⟨ now setoid_rewrite <- free_theorem_3 ⟩
  (select (mapLeft (flip (rev_f_ap ∘ flip t)) <$>
           (Left <$> (fmap[ Select F] comp (fmap[ Select F] rev_f_ap u))))
          (rev_f_ap <$> v)).
  ≡⟨ functor_laws ⟩
  (select (Left <$> ((flip (rev_f_ap ∘ flip t) ∘ comp ∘ rev_f_ap) <$> u))
          (rev_f_ap <$> v)).
  ≡⟨ reflexivity ⟩
  (((flip (rev_f_ap ∘ flip t) ∘ comp ∘ rev_f_ap) <$> u) <*> v).
  f_equal.
  f_equal.
  rewrite Heqz'', Heqt. clear Heqz'' z'' Heqt t.
  extensionalize.
Qed.


Theorem Select_ApplicativeLaws_composition :
  forall (A B C : Set)
  (u : Select F (B -> C)) (v : Select F (A -> B)) (w : Select F A),
  (pure[Select F] comp) <*> u <*> v <*> w = u <*> (v <*> w).
Proof.
  intros A B C u v w.
  `Begin
   (pure comp <*> u <*> v <*> w).
  ≡⟨ reflexivity ⟩
   ((pure comp <*> u) <*> v <*> w).
  ≡⟨ now rewrite Select_ap_fmap ⟩
   ((comp <$> u) <*> v <*> w).
  ≡⟨ reflexivity ⟩
   ((comp <$> u <*> v) <*> w).
  generalize dependent C. generalize dependent B. generalize dependent A.
  induction w.
  - intros B v C u.
  `Begin
   ((comp <$> u <*> v) <*> pure a).
  ≡⟨ reflexivity ⟩
   (select (Left <$> (comp <$> u <*> v)) (rev_f_ap <$> pure a)).
  ≡⟨ reflexivity ⟩
   (select (Left <$> (comp <$> u <*> v)) (pure (rev_f_ap a))).
  ≡⟨ reflexivity ⟩
   (either (rev_f_ap a) id <$> (Left <$> (comp <$> u <*> v))).
  ≡⟨ functor_laws ⟩
   ((either (rev_f_ap a) id ∘ Left) <$> (comp <$> u <*> v)).
  ≡⟨ trivial ⟩
   ((rev_f_ap a <$> ((comp <$> u) <*> v))).
  ≡⟨ reflexivity ⟩
   (rev_f_ap a <$> (select (Left <$> (comp <$> u)) (rev_f_ap <$> v))).
  ≡⟨ now rewrite <- free_theorem_1 ⟩
   ((select ((fmap (rev_f_ap a)) <$> (Left <$> (comp <$> u)))
            ((comp (rev_f_ap a)) <$> (rev_f_ap <$> v)))).
  ≡⟨ functor_laws ⟩
   ((select ((fmap (rev_f_ap a) ∘ Left) <$> (comp <$> u))
            (((comp (rev_f_ap a)) ∘ rev_f_ap) <$> v))).
  ≡⟨ trivial ⟩
   (select (Left <$> (comp <$> u))
           (((comp (rev_f_ap a)) ∘ rev_f_ap) <$> v)).
  ≡⟨ now rewrite <- (@free_theorem_3 _) ⟩
   (select ((mapLeft (flip (((comp (rev_f_ap a)) ∘ rev_f_ap)))) <$> (Left <$> (comp <$> u)))
           (rev_f_ap <$> v)).
  ≡⟨ now rewrite boring_details_3 ⟩
   (select ((mapLeft (flip (rev_f_ap ∘ (rev_f_ap a)))) <$> (Left <$> u))
           (rev_f_ap <$> v)).
  ≡⟨ now rewrite <- (@free_theorem_3 _) ⟩
   (select (Left <$> u)
           ((rev_f_ap ∘ (rev_f_ap a)) <$> v)).
  ≡⟨ functor_laws ⟩
   (select (Left <$> u) (rev_f_ap <$> (rev_f_ap a <$> v))).
  ≡⟨ reflexivity ⟩
   (u <*> (rev_f_ap a <$> v)).
  ≡⟨ trivial ⟩
   (u <*> ((either (rev_f_ap a) id ∘ Left) <$> v)).
  ≡⟨ functor_laws ⟩
   (u <*> (either (rev_f_ap a) id <$> (Left <$> v))).
  ≡⟨ reflexivity ⟩
   (u <*> (select (Left <$> v) (rev_f_ap <$> pure a))).
  ≡⟨ reflexivity ⟩
   (u <*> (v <*> pure a))
  `End.
  - intros X v C u.
  `Begin
   ((fmap comp u <*> v) <*> MkSelect w f).
  ≡⟨ reflexivity ⟩
   (select (Left <$> (fmap comp u <*> v)) (rev_f_ap <$> MkSelect w f)).
  ≡⟨ reflexivity ⟩
   (select (Left <$> (fmap comp u <*> v))
           (MkSelect ((fmap[Either _] rev_f_ap) <$> w) ((fmap[→_] rev_f_ap) <$> f))).
  ≡⟨ simpl select; now rewrite Select_select_equation_2 ⟩
   (MkSelect (select (law3_f <$> (Left <$> (fmap comp u <*> v)))
                     (law3_g <$> ((fmap[Either _] rev_f_ap) <$> w)))
             (law3_h <$> ((fmap[→_] rev_f_ap) <$> f))).
  ≡⟨ functor_laws ⟩
   (MkSelect (select ((law3_f ∘ Left) <$> (fmap comp u <*> v))
                     ((law3_g ∘ (fmap[Either _] rev_f_ap)) <$> w))
             ((law3_h ∘ (fmap[→_] rev_f_ap)) <$> f)).
  ≡⟨ now setoid_rewrite <- free_theorem_3 ⟩
   (MkSelect (select (mapLeft (flip (law3_g ∘ (fmap[Either _] rev_f_ap))) <$>
                       ((law3_f ∘ Left) <$> (fmap comp u <*> v)))
                     (rev_f_ap <$> w))
             ((law3_h ∘ (fmap[→_] rev_f_ap)) <$> f)).
  ≡⟨ functor_laws ⟩
   (MkSelect (select ((mapLeft (flip (law3_g ∘ (fmap rev_f_ap))) ∘ law3_f ∘ Left) <$>
                       (fmap comp u <*> v))
                     (rev_f_ap <$> w))
             ((law3_h ∘ (fmap[→_] rev_f_ap)) <$> f)).
  ≡⟨ rewrite <- comp_assoc; unfold law3_f; now rewrite Either_fmap_left_cancel ⟩
   (MkSelect (select ((mapLeft (flip (law3_g ∘ (fmap rev_f_ap))) ∘ Left) <$>
                       (fmap comp u <*> v))
                     (rev_f_ap <$> w))
             ((law3_h ∘ (fmap[→_] rev_f_ap)) <$> f)).
  ≡⟨ now rewrite mapLeft_drag_into_left ⟩
   (MkSelect (select ((Left ∘ flip (law3_g ∘ (fmap rev_f_ap))) <$>
                       (fmap comp u <*> v))
                     (rev_f_ap <$> w))
             ((law3_h ∘ (fmap[→_] rev_f_ap)) <$> f)).
  set (z := (flip (law3_g ∘ (fmap rev_f_ap)))) in *.
  ≡⟨ functor_laws ⟩
   (MkSelect (select (Left <$> (z <$> (fmap comp u <*> v)))
                     (rev_f_ap <$> w))
             ((law3_h ∘ (fmap[→_] rev_f_ap)) <$> f)).
  ≡⟨ reflexivity ⟩
   (MkSelect (select (Left <$> (z <$> (select (Left <$> fmap comp u)
                                              (rev_f_ap <$> v))))
                     (rev_f_ap <$> w))
             ((law3_h ∘ (fmap[→_] rev_f_ap)) <$> f)).
  ≡⟨ now rewrite <- free_theorem_1  ⟩
   (MkSelect (select (Left <$> (select (fmap[Either _] z <$> (Left <$> fmap comp u))
                                       (fmap[→_]       z <$> (rev_f_ap <$> v))))
                     (rev_f_ap <$> w))
             ((law3_h ∘ (fmap[→_] rev_f_ap)) <$> f)).
  ≡⟨ functor_laws  ⟩
   (MkSelect (select (Left <$> (select ((fmap[Either _] z ∘ Left)     <$> fmap comp u)
                                       ((fmap[→_]       z ∘ rev_f_ap) <$> v)))
                     (rev_f_ap <$> w))
             ((law3_h ∘ (fmap[→_] rev_f_ap)) <$> f)).
  ≡⟨ trivial ⟩
   (MkSelect (select (Left <$> (select (Left <$> fmap comp u)
                                       ((fmap[→_] z ∘ rev_f_ap) <$> v)))
                     (rev_f_ap <$> w))
             ((law3_h ∘ (fmap[→_] rev_f_ap)) <$> f)).
  ≡⟨ now setoid_rewrite <- free_theorem_3 ⟩
   (MkSelect (select (Left <$> (select ((mapLeft (flip (fmap[→_] z ∘ rev_f_ap))) <$>
                                        (Left <$> fmap comp u))
                                       (rev_f_ap <$> v)))
                     (rev_f_ap <$> w))
             ((law3_h ∘ (fmap[→_] rev_f_ap)) <$> f)).
  ≡⟨ functor_laws ⟩
   (MkSelect (select (Left <$> (select ((mapLeft (flip (fmap[→_] z ∘ rev_f_ap)) ∘ Left) <$>
                                        (fmap comp u))
                                       (rev_f_ap <$> v)))
                     (rev_f_ap <$> w))
             ((law3_h ∘ (fmap[→_] rev_f_ap)) <$> f)).
  ≡⟨ reflexivity ⟩
   (MkSelect (select (Left <$> (select ((Left ∘ (flip (fmap[→_] z ∘ rev_f_ap))) <$>
                                        (fmap comp u))
                                       (rev_f_ap <$> v)))
                     (rev_f_ap <$> w))
             ((law3_h ∘ (fmap[→_] rev_f_ap)) <$> f)).
  ≡⟨ functor_laws ⟩
   (MkSelect (select (Left <$> (select (Left <$> ((flip (fmap[→_] z ∘ rev_f_ap)) <$>
                                        (fmap comp u)))
                                       (rev_f_ap <$> v)))
                     (rev_f_ap <$> w))
             ((law3_h ∘ (fmap[→_] rev_f_ap)) <$> f)).
  ≡⟨ functor_laws ⟩
   (MkSelect (select (Left <$> (select (Left <$> (((flip (fmap[→_] z ∘ rev_f_ap)) ∘ comp) <$>
                                        u))
                                       (rev_f_ap <$> v)))
                     (rev_f_ap <$> w))
             ((law3_h ∘ (fmap[→_] rev_f_ap)) <$> f)).
  assert ((((flip (fmap[→_] z ∘ rev_f_ap)) ∘ comp) <$> u) =
          ((fun f g => Either_bimap ((flip pair) (f ∘ g)) (f ∘ g)) <$> u)) as H.
  { f_equal. extensionalize. }
  ≡⟨ now rewrite H; clear H ⟩
   (MkSelect (select (Left <$> (select (Left <$>
                               ((fun f g => Either_bimap ((flip pair) (f ∘ g)) (f ∘ g)) <$> u))
                                       (rev_f_ap <$> v)))
                     (rev_f_ap <$> w))
             ((law3_h ∘ (fmap[→_] rev_f_ap)) <$> f)).
  subst z. set (z' := (fun f g => Either_bimap ((flip pair) (f ∘ g)) (f ∘ g))) in *.
  ≡⟨ now rewrite <- free_theorem_3_MkSelect ⟩
   (MkSelect ((mapLeft (flip (law3_h ∘ (fmap[→_] rev_f_ap)))) <$>
              (select (Left <$> (select (Left <$> (z' <$> u))
                                        (rev_f_ap <$> v)))
                      (rev_f_ap <$> w)))
             (rev_f_ap <$> f)).
  ≡⟨ now rewrite <- free_theorem_1 ⟩
   (MkSelect ((select ((fmap[Either _]
                       (mapLeft (flip (law3_h ∘ (fmap[→_] rev_f_ap))))) <$>
                       (Left <$> (select (Left <$> (z' <$> u))
                                         (rev_f_ap <$> v))
                      ))
                      ((fmap[→_] (mapLeft (flip (law3_h ∘ (fmap[→_] rev_f_ap))))) <$>
                       (rev_f_ap <$> w))))
             (rev_f_ap <$> f)).
  set (p := fmap[→_] (mapLeft (flip (law3_h ∘ (fmap[→_] rev_f_ap))))) in *.
  ≡⟨ functor_laws ⟩
   (MkSelect (select (Left <$> (select (Left <$> (z' <$> u))
                                         (rev_f_ap <$> v))
                     )
                     ((p ∘ rev_f_ap) <$> w)
             )
             (rev_f_ap <$> f)).
  ≡⟨ now setoid_rewrite <- free_theorem_3 ⟩
   (MkSelect (select (mapLeft (flip (p ∘ rev_f_ap)) <$>
                              (Left <$> (select (Left <$> (z' <$> u))
                                                (rev_f_ap <$> v)))
                     )
                     (rev_f_ap <$> w)
             )
             (rev_f_ap <$> f)).
  ≡⟨ functor_laws ⟩
   (MkSelect (select (((mapLeft (flip (p ∘ rev_f_ap)) ∘ Left) <$>
                                (select (Left <$> (z' <$> u))
                                        (rev_f_ap <$> v)))
                     )
                     (rev_f_ap <$> w)
             )
             (rev_f_ap <$> f)).
  ≡⟨ now rewrite mapLeft_drag_into_left ⟩
   (MkSelect (select (((Left ∘ flip (p ∘ rev_f_ap)) <$> (select (Left <$> (z' <$> u))
                                                               (rev_f_ap <$> v)))
                     )
                     (rev_f_ap <$> w)
             )
             (rev_f_ap <$> f)).
  ≡⟨ functor_laws ⟩
   (MkSelect (select ((Left <$> (flip (p ∘ rev_f_ap) <$>
                       (select (Left <$> (z' <$> u))
                               (rev_f_ap <$> v))))
                     )
                     (rev_f_ap <$> w)
             )
             (rev_f_ap <$> f)).
  ≡⟨ now setoid_rewrite <- free_theorem_1 ⟩
   (MkSelect (select ((Left <$>
                       (select ((fmap (flip (p ∘ rev_f_ap))) <$> (Left <$> (z' <$> u)))
                               ((fmap[→_] (flip (p ∘ rev_f_ap))) <$> (rev_f_ap <$> v))))
                     )
                     (rev_f_ap <$> w)
             )
             (rev_f_ap <$> f)).
  ≡⟨ functor_laws; now rewrite Either_fmap_left_cancel ⟩
   (MkSelect (select ((Left <$>
                       (select (Left <$> (z' <$> u))
                               ((fmap[→_] (flip (p ∘ rev_f_ap)) ∘ rev_f_ap) <$> v)))
                     )
                     (rev_f_ap <$> w)
             )
             (rev_f_ap <$> f)).
  ≡⟨ now setoid_rewrite <- free_theorem_3 ⟩
   (MkSelect (select ((Left <$> (select
      (mapLeft (flip (fmap[→_] (flip (p ∘ rev_f_ap)) ∘ rev_f_ap)) <$> (Left <$> (z' <$> u)))
      (rev_f_ap <$> v)))
                     )
                     (rev_f_ap <$> w)
             )
             (rev_f_ap <$> f)).
  ≡⟨ functor_laws; now rewrite mapLeft_drag_into_left ⟩
   (MkSelect (select ((Left <$> (select
      ((Left <$> ((flip (fmap[→_] (flip (p ∘ rev_f_ap)) ∘ rev_f_ap)) <$> (z' <$> u))))
      (rev_f_ap <$> v)))
                     )
                     (rev_f_ap <$> w)
             )
             (rev_f_ap <$> f)).
  ≡⟨ functor_laws ⟩
   (MkSelect (select ((Left <$> (select
      ((Left <$> (((flip (fmap[→_] (flip (p ∘ rev_f_ap)) ∘ rev_f_ap)) ∘ z') <$> u)))
      (rev_f_ap <$> v)))
                     )
                     (rev_f_ap <$> w)
             )
             (rev_f_ap <$> f)).
  remember (flip (fmap[→_] (flip (p ∘ rev_f_ap)) ∘ rev_f_ap) ∘ z') as z''.
  subst z'. subst p.
  ≡⟨ reflexivity ⟩
   (MkSelect (((z'' <$> u) <*> v) <*> w)
             (rev_f_ap <$> f)).
  remember ((fun y =>
            fmap[→_]
              (fmap[→_]
                 (mapLeft
                    (flip
                       (((law3_h ∘ fmap[→_] (@rev_f_ap X C)) ∘ law3_h) ∘ fmap[→_] rev_f_ap))))
              ((((fmap[→_] law3_g ∘ fmap[→_] (fmap (@rev_f_ap X C))) ∘ law3_g) ∘
                  fmap[ Either B] (@rev_f_ap A X)) y))) as t.
  ≡⟨ now setoid_rewrite <- ap_comp_boring_details ⟩
  (MkSelect
    (fmap comp (rev_f_ap <$> u) <*> (flip t <$> v) <*> w)
    (rev_f_ap <$> f)
  ).
  ≡⟨ now rewrite IHw ⟩
  (MkSelect
    ((rev_f_ap <$> u) <*> ((flip t <$> v) <*> w))
    (rev_f_ap <$> f)
  ).
  ≡⟨ reflexivity ⟩
  (MkSelect
    (select (Left <$> (rev_f_ap <$> u))
            (rev_f_ap <$> ((flip t <$> v) <*> w)))
    (rev_f_ap <$> f)
  ).
  ≡⟨ functor_laws ⟩
  (MkSelect
    (select (mapLeft rev_f_ap <$> (Left <$> u))
            (rev_f_ap <$> ((flip t <$> v) <*> w)))
    (rev_f_ap <$> f)
  ).
  ≡⟨ trivial ⟩
  (MkSelect
    (select (mapLeft (flip id) <$> (Left <$> u))
            (rev_f_ap <$> ((flip t <$> v) <*> w)))
    (rev_f_ap <$> f)
  ).
  ≡⟨ now setoid_rewrite <- free_theorem_3 ⟩
  (MkSelect
    (select (Left <$> u)
            (id <$> ((flip t <$> v) <*> w)))
    (rev_f_ap <$> f)
  ).
  ≡⟨ functor_laws ⟩
  (MkSelect
    (select (Left <$> u)
            ((flip t <$> v) <*> w))
    (rev_f_ap <$> f)
  ).
  ≡⟨ reflexivity ⟩
  (MkSelect
    (select (Left <$> u)
       ((select (Left <$> (flip t <$> v))
                (rev_f_ap <$> w))))
    (rev_f_ap <$> f)
  ).
  ≡⟨ functor_laws; now rewrite mapLeft_drag_into_left ⟩
  (MkSelect
    (select (Left <$> u)
       ((select (mapLeft (flip t) <$> (Left <$> v))
                (rev_f_ap <$> w))))
    (rev_f_ap <$> f)
  ).
  ≡⟨ now setoid_rewrite <- free_theorem_3 ⟩
  (MkSelect
    (select (Left <$> u)
       ((select (Left <$> v)
                (t <$> w))))
    (rev_f_ap <$> f)
  ).
  ≡⟨ functor_laws; now setoid_rewrite <- Heqt ⟩
  (MkSelect
    (select ((Left <$> u))
       ((select (Left <$> v)
                (((fmap[→_] (fmap[→_] (mapLeft (flip (law3_h  ∘ (fmap[→_] rev_f_ap) ∘ law3_h ∘ (fmap[→B] rev_f_ap))))) <$> ((fmap law3_g ∘ fmap[→_] (fmap[Either _] rev_f_ap) ∘
                       law3_g ∘ fmap rev_f_ap) <$> w)))))))
    (rev_f_ap <$> f)
  ).
  ≡⟨ admit ⟩
  (* ≡⟨ now setoid_rewrite <- (free_theorem_1_left _ _ _ (Select F) *)
  (*     Select_Selective (@Select_FunctorLaws F FFunctor FFunctorLaws) _ v) ⟩ *)
  (MkSelect
    (select ((Left <$> u))
       ((fmap[→_] (mapLeft (flip (law3_h  ∘ (fmap[→_] rev_f_ap) ∘ law3_h ∘ (fmap[→B] rev_f_ap))))) <$>
         (select (Left <$> v)
                ((fmap law3_g ∘ fmap[→_] (fmap[Either _] rev_f_ap) ∘
                       law3_g ∘ fmap rev_f_ap) <$> w))))
    (rev_f_ap <$> f)
  ).
  (* ≡⟨ now rewrite <- (free_theorem_1_left _ _ _ (Select F) *)
  (*     Select_Selective (@Select_FunctorLaws F FFunctor FFunctorLaws)) ⟩ *)
  ≡⟨ admit ⟩
  (MkSelect
    (mapLeft (flip (law3_h  ∘ (fmap[→_] rev_f_ap) ∘ law3_h ∘ (fmap[→B] rev_f_ap))) <$>
      select (Left <$> u)
       ((select (Left <$> v)
                ((fmap law3_g ∘ fmap[→_] (fmap[Either _] rev_f_ap) ∘
                       law3_g ∘ fmap rev_f_ap) <$> w))))
    (rev_f_ap <$> f)
  ).
  ≡⟨ now repeat rewrite <- free_theorem_3_MkSelect ⟩
  (MkSelect
    (select (Left <$> u)
       ((select (Left <$> v)
                ((fmap law3_g ∘ fmap[→_] (fmap[Either _] rev_f_ap) ∘
                       law3_g ∘ fmap rev_f_ap) <$> w))))
    ((law3_h  ∘ (fmap[→_] rev_f_ap) ∘ law3_h ∘ (fmap[→B] rev_f_ap)) <$> f)
  ).
  ≡⟨ now functor_laws ⟩
  (MkSelect
    (select (Left <$> u)
       ((select ((fmap law3_g) <$> (Left <$> v))
                ((fmap law3_g) <$>
                 ((fmap[→_] (fmap[Either _] rev_f_ap) ∘ law3_g ∘ fmap rev_f_ap) <$> w)))))
    ((law3_h  ∘ (fmap[→_] rev_f_ap) ∘ law3_h ∘ (fmap[→B] rev_f_ap)) <$> f)
  ).
  ≡⟨ now setoid_rewrite <- free_theorem_1 ⟩
  (MkSelect
    (select (Left <$> u)
       (law3_g <$>
          (select (Left <$> v)
                  (((fmap[→_] (fmap[Either _] rev_f_ap) ∘ law3_g ∘ fmap rev_f_ap) <$> w)))))
    ((law3_h  ∘ (fmap[→_] rev_f_ap) ∘ law3_h ∘ (fmap[→B] rev_f_ap)) <$> f)
  ).
  ≡⟨ now functor_laws ⟩
  (MkSelect
    (select (Left <$> u)
       (law3_g <$>
          (select ((fmap[Either (A -> X)] (fmap[Either _] (@rev_f_ap X C))) <$> (Left <$> v))
                  (fmap[Select F] (fmap[→_] (fmap[Either _] rev_f_ap))
                      (fmap[ Select F] (law3_g ∘ fmap rev_f_ap) w)))))
    ((law3_h  ∘ (fmap[→_] rev_f_ap) ∘ law3_h ∘ (fmap[→B] rev_f_ap)) <$> f)
  ).
  ≡⟨ now setoid_rewrite <- free_theorem_1 ⟩
  (MkSelect
    (select (Left <$> u)
       (law3_g <$>
          ((fmap[Either _] rev_f_ap) <$>
             (select (Left <$> v)
                (fmap[ Select F] (law3_g ∘ fmap rev_f_ap) w)))))
    ((law3_h  ∘ (fmap[→_] rev_f_ap) ∘ law3_h ∘ (fmap[→_] rev_f_ap)) <$> f)
  ).
  ≡⟨ unfold law3_f; now (repeat setoid_rewrite <- (Either_fmap_left_cancel _ _ _ Right)) ⟩
  (MkSelect
    (select (fmap[ Select F] (law3_f ∘ Left) u)
       (law3_g <$>
          ((fmap[Either _] rev_f_ap) <$>
             (select (fmap[ Select F] (law3_f ∘ Left) v)
                (fmap[ Select F] (law3_g ∘ fmap rev_f_ap) w)))))
    ((law3_h  ∘ (fmap[→_] rev_f_ap) ∘ law3_h ∘ (fmap[→_] rev_f_ap)) <$> f)
  ).
  ≡⟨ functor_laws ⟩
  (MkSelect
    (select (fmap[ Select F] law3_f (Left <$> u))
       (law3_g <$>
          ((fmap[Either _] rev_f_ap) <$>
             (select (fmap[ Select F] (law3_f ∘ Left) v)
                (fmap[ Select F] (law3_g ∘ fmap rev_f_ap) w)))))
    (law3_h <$>
       ((fmap[→_] rev_f_ap) <$>
          (fmap (law3_h ∘ (fmap[→_] rev_f_ap)) f)))).
  ≡⟨ simpl; now simp Select_select ⟩
   (select (Left <$> u)
           (MkSelect ((fmap[Either _] rev_f_ap) <$>
                        (select ((law3_f ∘ Left) <$> v)
                                ((law3_g ∘ fmap[Either _] rev_f_ap) <$> w)))
                     ((fmap[→_] rev_f_ap) <$> ((law3_h ∘ (fmap[→_] rev_f_ap)) <$> f))
           )
   ).
  ≡⟨ reflexivity ⟩
   (select (Left <$> u)
           (rev_f_ap <$> (MkSelect (select ((law3_f ∘ Left) <$> v)
                                           ((law3_g ∘ fmap[Either _] rev_f_ap) <$> w))
                                   ((law3_h ∘ (fmap[→_] rev_f_ap)) <$> f)))).
  ≡⟨ reflexivity ⟩
   (u <*> (MkSelect (select ((law3_f ∘ Left) <$> v)
                            ((law3_g ∘ fmap[Either _] rev_f_ap) <$> w))
                    ((law3_h ∘ (fmap[→_] rev_f_ap)) <$> f))).
  ≡⟨ functor_laws ⟩
   (u <*> (MkSelect (select (fmap[Select F] law3_f (Left <$> v))
                            (fmap[Select F] law3_g ((fmap[Either _] rev_f_ap) <$> w)))
                    (fmap[F] law3_h ((fmap[→_] rev_f_ap) <$> f)))).
  ≡⟨ simpl; now simp Select_select ⟩
   (u <*> (select (Left <$> v)
                  (MkSelect ((fmap[Either _] rev_f_ap) <$> w)
                            ((fmap[→_] rev_f_ap) <$> f)))).
  ≡⟨ reflexivity ⟩
   (u <*> (select (Left <$> v) (rev_f_ap <$> MkSelect w f))).
  ≡⟨ reflexivity ⟩
   (u <*> (v <*> MkSelect w f))
  `End.
(* Qed. *)
Admitted.

End Select_ApplicativeLaws_Proofs.

Check Select_FunctorLaws.

Import ApplicativeLaws.

Check Select_FunctorLaws.


Global Program Instance Select_ApplicativeLaws (F : Set -> Set)
       (HF : Functor F) (HFL : FunctorLaws F) :
  ApplicativeLaws (Select F).
  (* (@ApplicativeLaws (Select F) (@Select_Applicative F H)). *)
Obligation 1.
extensionality x.
`Begin
  (Select_ap (Pure (@id _)) x).
≡⟨ reflexivity ⟩
 (pure (@id _) <*> x).
≡⟨ now rewrite Select_ap_fmap ⟩
  (fmap id x).
≡⟨ now rewrite fmap_id ⟩
 (id x)
`End.
Qed.
Obligation 2.
(* apply (Select_ApplicativeLaws_composition _ _ _). *)
(* Qed. *)
Admitted.
Obligation 4.
apply (@Select_ApplicativeLaws_interchange _ _ _).
Qed.
Obligation 5.
(** pure f <*> x = f <$> x *)
Proof.
extensionality x. apply (@Select_ap_fmap _ _ _).
Qed.
