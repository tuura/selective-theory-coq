This is a Coq formalisation of Selective Applicative Functors, containing proof of `Functor`, `Applicative` and `Selective` laws for a number of instances.

## Build instructions

To play with the definitions and proofs, you'll need to have the [Coq proof assistant](https://coq.inria.fr/download) installed. You will also need the [`Equations` plug-in](https://github.com/mattam82/Coq-Equations). The proofs can be checked by running `make`.

## Free Rigid Selective Functors

The most interesting thing in this repo is the data type formalising [free rigid selective
functors](https://github.com/tuura/selective-theory-coq/blob/master/src/Control/Selective/Rigid.v)

```
Inductive Select (F : Type -> Type) (A : Type) :=
    Pure   : A -> Select F A
  | MkSelect : forall B, Select F (B + A) -> F (B -> A) -> Select F A.
```

and the proofs it is a lawful instance of [`Functor`](https://github.com/tuura/selective-theory-coq/blob/master/src/Control/Selective/Rigid/Proofs/Functor.v), [`Applicative`](https://github.com/tuura/selective-theory-coq/blob/master/src/Control/Selective/Rigid/Proofs/Applicative.v) and (proof to be completed) [`Selective`](https://github.com/tuura/selective-theory-coq/blob/master/src/Control/Selective/Rigid/Proofs/Selective.v).

## Free Theorems

The proofs for free rigid selective functors rely no three free theorems which
hold by parametricity and admitted as axioms. See [`SelectiveParametricity`](https://github.com/tuura/selective-theory-coq/blob/bf854a459e423e86df6703e0b809d80d133ae6f9/src/Control/Selective.v#L43) for details. We also reformulate these theorems for the data constructor [`MkSelect`](https://github.com/tuura/selective-theory-coq/blob/master/src/Control/Selective/Rigid/Parametricity.v)

# Acknowledgements

We borrowed a number of definitions and tricks from @jwiegley's
[coq-haskell](https://github.com/jwiegley/coq-haskell) library.
