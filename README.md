This is a supplementary material for the paper entitled Selective Applicative Functors, containing Coq proofs for various selective instances. Take a look at [this repository](https://github.com/snowleopard/selective) for the paper draft and Haskell implementation.

# Try it out

To play with the definitions and proofs, you'll need to have to install the Coq proof assistant. The proofs can me checked by executing `make`.

Instances currently proven: [`Over`](https://github.com/tuura/selective-theory-coq/blob/master/src/Data/Over.v), [`Over`](https://github.com/tuura/selective-theory-coq/blob/master/src/Data/Under.v), [`Validation`](https://github.com/tuura/selective-theory-coq/blob/master/src/Data/Validation.v).
Free rigid selective construction in progress.

# References

We borrowed many definitions form the magnificent
[coq-haskell](https://github.com/jwiegley/coq-haskell) library.
