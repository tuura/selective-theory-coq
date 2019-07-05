Generalizable All Variables.

Require Import Data.Functor.
Require Import Control.Applicative.
Require Import FunctionalExtensionality.

Notation Either := sum (only parsing).
Notation Left   := inl (only parsing).
Notation Right  := inr (only parsing).

(* Inductive Either (A B : Set) : Set := *)
(*     Left  : A -> Either A B *)
(*   | Right : B -> Either A B. *)

Arguments Left {_} {_}.
Arguments Right {_} {_}.

(* Notation "x + y" := (Either x y) : type_scope. *)

Definition EitherFn X Y :=
  forall Z, (X -> Z) -> (Y -> Z) -> Z.

Definition mkLeft {X Y : Type} (x : X) :=
  fun (Z : Type) (l : X -> Z) (_ : Y -> Z) => l x.

Compute (mkLeft 1).

Check EitherFn nat nat.


(* Definition isLeft  `(x : a + b) : bool := if x then true else false. *)
(* Definition isRight `(x : a + b) : bool := if x then false else true. *)

Definition either {a b c : Type} (f : a -> c) (g : b -> c) (x : a + b) : c :=
  match x with
  | Left a => f a
  | Right b => g b
  end.

Definition mapLeft {a b c : Type} (f : a -> c) (x : a + b) : c + b :=
  match x with
  | Left l => Left (f l)
  | Right r => Right r
  end.

Definition mapRight {a b c : Type} (f : b -> c) (x : a + b) : a + c :=
  match x with
  | Left l => Left l
  | Right r => Right (f r)
  end.

Definition Either_map {E X Y : Type} (f : X -> Y) (x : Either E X) : Either E Y :=
  match x with
  | Left e   => Left e
  | Right x' => Right (f x')
  end.

Lemma Either_map_comp_x :
  forall (E A B C : Type)
    (f : B -> C) (g : A -> B) (x : E + A),
    Either_map f (Either_map g x) = Either_map (f \o g) x.
Proof.
  intros E A B C f g x.
  destruct x; trivial.
Qed.

(* Lemma id_x_is_x {A : Type}: *)
(*   forall (x : A), id x = x. *)
(* Proof. *)
(*   intros x. reflexivity. *)
(* Qed. *)

Lemma Either_map_id {E X : Type} :
  @Either_map E X X id = id.
Proof.
  extensionality x.
  destruct x;
  reflexivity.
Qed.

Definition Either_bimap {A B X Y : Type} (f : A -> B) (g : X -> Y) (x : Either A X) : Either B Y :=
  match x with
  | Left a  => Left (f a)
  | Right x => Right (g x)
  end.

Lemma Either_bimap_id :
  forall (A B : Type),
    Either_bimap (@id A) (@id B) = id.
Proof.
  intros A B.
  extensionality x.
  destruct x; trivial.
Qed.

Definition Either_ap {E X Y : Type} (f : Either E (X -> Y)) (x : Either E X)
  : Either E Y :=
  match f with
  | Left e   => Left e
  | Right f' => match x with
    | Left e   => Left e
    | Right x' => Right (f' x')
    end
  end.

Definition Either_join {E X : Type} (x : Either E (Either E X)) : Either E X :=
  match x with
  | Left e           => Left e
  | Right (Left e)   => Left e
  | Right (Right x') => Right x'
  end.

Instance Either_Functor {E} : Functor (Either E) :=
{ fmap := @Either_map E
}.

Import FunctorLaws.

Program Instance Either_FunctorLaws {E} : FunctorLaws (Either E).
Obligation 1.
extensionality x. now destruct x.
Defined.
Obligation 2.
extensionality x. now destruct x.
Defined.

Lemma Either_map_to_fmap :
  forall (A B C : Type)
         (f : B -> C),
    @Either_map A B C f = fmap f.
Proof. now simpl fmap. Qed.

Instance Either_Applicative {E} : Applicative (Either E) :=
{ is_functor := Either_Functor
; pure := @Right E
; ap := @Either_ap E
}.

Import ApplicativeLaws.

Program Instance Either_ApplicativeLaws {E} : ApplicativeLaws (Either E).
Obligation 1.
extensionality x. now destruct x.
Defined.
Obligation 2.
destruct w; destruct v; destruct u; trivial.
Defined.
