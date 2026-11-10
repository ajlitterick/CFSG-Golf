module

public import Mathlib.GroupTheory.Perm.Basic

public section

namespace CFSG.StandardType.SporadicShape.PermCover

open Equiv

@[expose] def mat {n : ℕ} (σ : Perm (Fin n)) : Perm (Fin n) :=
  let f : Array (Fin n) := Array.ofFn fun i => σ i
  let g : Array (Fin n) := Array.ofFn fun i => σ⁻¹ i
  ⟨fun i => f.getD i.1 i, fun i => g.getD i.1 i, fun i => by
      simp [f, g], fun i => by simp [f, g]⟩


end CFSG.StandardType.SporadicShape.PermCover
