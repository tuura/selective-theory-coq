Require Import Hask.Prelude.
Require Import Data.Functor.

Notation "→ B" := (Env B) (at level 0).

Tactic Notation
  "`Begin " constr(lhs) := idtac.

Tactic Notation
  "≡⟨ " tactic(proof) "⟩" constr(lhs) :=
  (stepl lhs by proof).

Tactic Notation
  "≡⟨ " tactic(proof) "⟩" constr(lhs) "`End" :=
  (now stepl lhs by proof).
