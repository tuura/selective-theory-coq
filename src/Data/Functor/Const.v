Require Import Hask.Data.Functor.

Generalizable All Variables.

Definition Const (c a : Set) := c.

Program Instance Const_Functor (c : Set) : Functor (Const c) := {
  fmap := fun _ _ _ => id
}.
