module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.ASVolI.ChH

open Equiv


private def OrderThree (σ : Perm (Fin 8)) : Prop := σ * σ * σ = 1 ∧ σ ≠ 1

private instance (σ : Perm (Fin 8)) : Decidable (OrderThree σ) :=
  inferInstanceAs (Decidable (σ * σ * σ = 1 ∧ σ ≠ 1))


end CFSG.ASVolI.ChH
