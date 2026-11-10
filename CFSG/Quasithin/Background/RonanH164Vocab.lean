module

public import CFSG.Quasithin.Background.RonanH163Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143

@[expose] def FullTranspCenter {V : Type*} [CommGroup V] (G X : Subgroup (MulAut V))
    (A V₁ : Subgroup V) : Prop :=
  (∀ g ∈ X, ∀ x ∈ A, g x * x⁻¹ ∈ V₁) ∧
  (∀ τ : MulAut ↥A, (∀ x : ↥A, ((τ x : ↥A) : V) * ((x : ↥A) : V)⁻¹ ∈ V₁) →
    ∃ g ∈ X, ∀ x : ↥A, g (x : V) = ((τ x : ↥A) : V)) ∧
  (∀ g ∈ X, (∀ x ∈ A, g x = x) → g = 1) ∧
  (∀ h ∈ G, ∀ g ∈ X, h * g * h⁻¹ ∈ X)

@[expose] def IsDualOfConj {V : Type*} [CommGroup V] {Γ : Subgroup P24} (ρ : ↥Γ →* MulAut V)
    (G : Subgroup P24) (A B : Subgroup V) (K : Subgroup P24) : Prop :=
  ∃ pr : V → P24 → ZMod 2,
    (∀ x ∈ A, ∀ k ∈ K, ∀ k' ∈ K, pr x (k * k') = pr x k + pr x k') ∧
    (∀ x ∈ A, ∀ x' ∈ A, ∀ k ∈ K, pr (x * x') k = pr x k + pr x' k) ∧
    (∀ x ∈ B, ∀ k ∈ K, pr x k = 0) ∧
    (∀ x ∈ A, x ∉ B → ∃ k ∈ K, pr x k ≠ 0) ∧ (∀ k ∈ K, k ≠ 1 → ∃ x ∈ A, pr x k ≠ 0) ∧
    ∀ g : ↥Γ, (g : P24) ∈ G → ∀ x ∈ A, ∀ k ∈ K, pr (ρ g x) ((g : P24) * k * (g : P24)⁻¹) = pr x k

@[expose] def Chain164 {V : Type*} [CommGroup V] {Γ : Subgroup P24} (ρ : ↥Γ →* MulAut V)
    (Hx : Finset (Fin 24)) (V₅ V₆ : Subgroup V) : Prop :=
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Hx))) ⊥ (fixV (rImg ρ (KY Γ Hx))) ∧
  rk ↥(fixV (rImg ρ (KY Γ Hx))) = 1 ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Hx))) (fixV (rImg ρ (KY Γ Hx))) V₅ ∧
  rk ↥V₅ = 5 ∧ V₅ = commV (rImg ρ (KY Γ Hx)) ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Hx))) V₅ V₆ ∧ rk ↥V₆ = 6 ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Hx))) V₆ ⊤


end CFSG.Quasithin.RonanH163
