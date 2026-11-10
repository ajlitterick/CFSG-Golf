module

public import CFSG.ClassicalInvolution.Asc77.AscHypOmegaTwin
public import CFSG.ClassicalInvolution.Asc77.WP2Stand

public section

namespace CFSG.ClassicalInvolution.Asc77.AscHypOmega

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

section Fusion

variable {G : Type} [Group G]


@[expose] def FusionAt (K : Subgroup G) (z : G) : Prop :=
  HasTwin K z → ∀ J ∈ CoreAssembly.conjClass K, ∀ t : G, IsUniqueInvolution J t → t ≠ z →
    ∀ v ∈ J, IsPGroup 2 (Subgroup.zpowers v) → (¬ ∀ w ∈ J, v * w = w * v) →
      v * z = z * v → v ∈ Subgroup.normalizer (K : Set G)

end Fusion

@[expose] def ClassicalFusionStmt (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → FusionAt K z

section Proofs

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}


theorem omega5At_of_fusionAt (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h₀ : IsClassicalMember p f K z)
    (hfus : FusionAt K z) : Omega5At (CoreAssembly.conjClass K) K z := by
  intro J hJ _ v hvJ hvnc hv2 hvz
  have hU₀ := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq h₀
  obtain ⟨b, rfl⟩ := CoreAssembly.single_class K J hJ
  have hUb := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq (h₀.conj b)
  by_cases ht : b * z * b⁻¹ = z
  · refine normalizer_of_twins hp2 hq h₀ (CoreAssembly.mem_conjClass_self K) hJ hU₀ ?_ hvJ
    rw [← ht]
    exact hUb
  · by_cases htw : HasTwin K z
    · exact hfus htw _ hJ _ hUb ht v hvJ hv2 hvnc hvz
    · exact centralizer_le_normalizer_of_not_hasTwin hU₀ htw
        (Subgroup.mem_centralizer_singleton_iff.mpr hvz)

theorem hypOmegaMod_of_fusionAt (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hz : IsClassicalMember p f K z)
    (hfus : FusionAt K z) : HypOmegaMod p f (CoreAssembly.conjClass K) where
  conjInvariant := conjInvariant_conjClass K
  classical := fun L hL => by
    obtain ⟨g, rfl⟩ := CoreAssembly.single_class K L hL
    exact ⟨g * z * g⁻¹, hz.conj g⟩
  omega4 := fun _ h₁ _ hJ hne => omega4_of_classical hp2 hq hz h₁ hJ hne
  omega5 := omega5_of_omega5At hp2 hq hz (omega5At_of_fusionAt hp2 hq hz hfus)


end Proofs

@[expose] def HypOmegaAllStmt (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → HypOmegaMod p f (CoreAssembly.conjClass K)

theorem hypOmegaAllStmt_of_fusion (h : ClassicalFusionStmt p f) : HypOmegaAllStmt p f :=
  fun G _ _ _ hnab hp2 hq K z hz hbelow =>
    hypOmegaMod_of_fusionAt hp2 hq hz (h G hnab hp2 hq K z hz hbelow)

theorem hypOmegaModD_of_all (h : HypOmegaAllStmt p f) : HypOmegaModD p f :=
  fun G _ _ _ K z hb => h G hb.nonabelian hb.odd hb.five K z hb.member hb.below

theorem hypOmegaModD_of_fusion (h : ClassicalFusionStmt p f) : HypOmegaModD p f :=
  hypOmegaModD_of_all (hypOmegaAllStmt_of_fusion h)


end CFSG.ClassicalInvolution.Asc77.AscHypOmega
