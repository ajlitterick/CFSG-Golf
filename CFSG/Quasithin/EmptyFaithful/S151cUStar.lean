module

public import CFSG.Quasithin.EmptyFaithful.S151cSetting

public section

namespace CFSG.Quasithin

open CFSG.Open

section UStar151c

structure UStar {W : Type*} [CommGroup W] [Finite W] (Xr H Ξ : Subgroup (MulAut W)) : Prop where
  isP : IsPGroup 2 H
  hU : ∀ z : W, z ∈ fixV H → z ≠ 1 → ∀ ψ ∈ Xr, ψ z = z → ψ ∈ Ξ
  star : ∀ B : Subgroup W, B ≠ ⊥ → (∀ ψ ∈ Xr, ∀ w ∈ B, ψ w ∈ B) →
    ¬ B ≤ Subgroup.closure {x | ∃ ψ ∈ Ξ, ∃ z ∈ fixV H ⊓ B, ψ z = x}

variable {V : Type*} [CommGroup V] [Finite V] {X Tb Xc : Subgroup (MulAut V)}

omit [Finite V] in
theorem le_stabSub_of_invariant {U : Subgroup V} (hU : ∀ x ∈ X, ∀ u ∈ U, x u ∈ U) :
    X ≤ stabSub U := by
  intro x hx u
  refine ⟨fun h => ?_, fun h => hU x hx u h⟩
  have := hU x⁻¹ (X.inv_mem hx) _ h
  simpa using this


end UStar151c

end CFSG.Quasithin
