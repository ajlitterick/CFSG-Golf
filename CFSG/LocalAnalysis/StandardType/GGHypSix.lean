module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Abstract

variable {U : Type*} [Group U] (Δ : UniversalRootDatum U) {G : Type*} [Group G]

@[expose] def GGTorusOnRoot (ψ : U →* G) (c : G) (γ : Fin Δ.rank → ℤ) (u : U) : Prop :=
  ∃ g ∈ ψ.range, ∃ h ∈ ggTorus Δ, ∀ z ∈ Δ.rootGroup γ,
    (c * g)⁻¹ * ψ (u * z * u⁻¹) * (c * g) = ψ (u * (h * z * h⁻¹) * u⁻¹)


variable {U' : Type*} [Group U'] (Δ' : UniversalRootDatum U')

@[expose] def GGRootMatch (ψ : U →* G) (ψ' : U' →* G) (δ : Fin Δ'.rank → ℤ)
    (γ : Fin Δ.rank → ℤ) (u : U) : Prop :=
  (∀ z ∈ Δ.rootGroup γ, ∃ z' ∈ Δ'.rootGroup δ, ψ' z' = ψ (u * z * u⁻¹)) ∧
    ∀ h' ∈ ggTorus Δ', ∃ h ∈ ggTorus Δ, ∀ z ∈ Δ.rootGroup γ, ∀ z' ∈ Δ'.rootGroup δ,
      ψ' z' = ψ (u * z * u⁻¹) → ψ' (h' * z' * h'⁻¹) = ψ (u * (h * z * h⁻¹) * u⁻¹)

variable {Δ Δ'} in
theorem ggTorusOnRoot_of_rootMatch {ψ : U →* G} {ψ' : U' →* G} (hle : ψ'.range ≤ ψ.range)
    {δ : Fin Δ'.rank → ℤ} (hδ : δ ∈ Δ'.roots) {γ : Fin Δ.rank → ℤ} {u : U}
    (hm : GGRootMatch Δ Δ' ψ ψ' δ γ u) {c : G} (hc : GGPsiInnerDiag Δ' ψ' c) :
    GGTorusOnRoot Δ ψ c γ u := by
  obtain ⟨g, hg, hall⟩ := hc
  obtain ⟨h', hh', hz'⟩ := hall δ hδ
  obtain ⟨h, hh, hcomp⟩ := hm.2 h' hh'
  refine ⟨g, hle hg, h, hh, fun z hz => ?_⟩
  obtain ⟨z', hz'm, heq⟩ := hm.1 z hz
  rw [← heq, hz' z' hz'm, hcomp z hz z' hz'm heq]

end Abstract

section Inputs

@[expose] def GGCompatPresented {U : Type*} [Group U] {G : Type*} [Group G]
    (Δ : UniversalRootDatum U) (ψ : U →* G) (K : Subgroup G) : Prop :=
  ∃ (t' : StatedLieTag) (n' f' : ℕ) (ψ' : (ggU t' n' f').K →* G),
    StatedLieAdmissible t' n' 2 f' ∧ 2 ≤ (ggU t' n' f').D.rank ∧
    ψ'.ker ≤ Subgroup.center (ggU t' n' f').K ∧ ψ'.range = K ∧
    ∃ δ ∈ (ggU t' n' f').D.roots, ∃ γ ∈ Δ.roots, ∃ u : U,
      GGRootMatch Δ (ggU t' n' f').D ψ ψ' δ γ u

@[expose] def GGRootDetect (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G),
    StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU t n f).K →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (t = .POmegaPlus ∧ n = 4 ∧ p = 3) →
    ∀ c ∈ Subgroup.normalizer (ψ.range : Set G),
      c ^ p ∈ Subgroup.centralizer (ψ.range : Set G) →
      ∀ γ ∈ (ggU t n f).D.roots, ∀ u : (ggU t n f).K, GGTorusOnRoot (ggU t n f).D ψ c γ u →
        GGPsiInnerDiag (ggU t n f).D ψ c


end Inputs

section Reduction


end Reduction

end CFSG.StandardType
