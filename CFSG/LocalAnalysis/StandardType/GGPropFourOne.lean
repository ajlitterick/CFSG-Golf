module

public import CFSG.LocalAnalysis.StandardType.GGPropFourOneThompson

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGFieldCase (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J X : Subgroup G) : Prop :=
  GGConfig p B Bs x L D J ∧ GGFieldNbrCanonical p B Bs x D J ∧
    X ≤ Subgroup.normalizer (Bs : Set G) ∧ Subgroup.centralizer (Bs : Set G) ≤ X ∧
    (X.subgroupOf (Subgroup.normalizer (Bs : Set G))).Normal ∧
    (∀ g ∈ X, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) ∧
    ¬ X ≤ Subgroup.centralizer (Bs : Set G)

@[expose] def GGFieldCaseData (p : ℕ) (Bs X M R U U₁ : Subgroup G) : Prop :=
  M = Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ∧
    IsPGroup p R ∧ R ≤ M ∧ (∀ Q : Subgroup G, Q ≤ M → IsPGroup p Q → R ≤ Q → Q = R) ∧
    U ≤ R ∧ R ≤ Subgroup.normalizer (U : Set G) ∧
    U₁ ≤ U ∧ IsMulCommutative U₁ ∧ (∀ A ∈ thompsonAbelianSubgroups U, A = U₁) ∧
    (∀ u : G, u ∈ Bs ⊓ Subgroup.centralizer (X : Set G) ↔ u ∈ U₁ ∧ u ^ p = 1) ∧
    (∀ A ∈ thompsonAbelianSubgroups R, ⁅⁅U₁, A⁆, A⁆ = ⊥ → A ≤ U)

end Defs


section Proof

variable {G : Type} [Group G] [Finite G]

theorem ggFieldCaseData_false {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hG : IsSimpleGroup G)
    (hnc : ∃ a b : G, a * b ≠ b * a) {Bs X M R U U₁ : Subgroup G}
    (hdata : GGFieldCaseData p Bs X M R U U₁)
    (ψ : Subgroup.normalizer (U₁ : Set G) →* Multiplicative (ZMod p)) (hψ : ψ ≠ 1) : False := by
  obtain ⟨hM, hRp, -, hmax, hUR, hRU, hU₁U, hU₁ab, hJU, hB₁, hrep⟩ := hdata
  obtain ⟨⟨S, rfl⟩, -, hwc⟩ := ggL47 hRp hmax hUR hRU hU₁U hU₁ab hJU hB₁ hM.ge hrep
  exact not_isSimpleGroup_of_isMulCommutative hp2 S (hU₁U.trans hUR) hwc hU₁ab ψ hψ hnc hG

end Proof


end CFSG.StandardType

end
