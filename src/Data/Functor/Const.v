Require Import Hask.Data.Functor.

Generalizable All Variables.

Definition Const (c a : Type) := c.

Program Instance Const_Functor (c : Type) : Functor (Const c) := {
  fmap := fun _ _ _ => id
}.
