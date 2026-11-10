module

public import CFSG.ClassicalInvolution.Uniform.UInduction
public import CFSG.ClassicalInvolution.Uniform.UOmega4
public import CFSG.ClassicalInvolution.Asc77.WP2Stand
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups commutatorElement

section HypOmega

variable {G : Type} [Group G]

structure HypOmegaModU (t : MemberType) (Ω : Set (Subgroup G)) : Prop where
  conjInvariant : ConjInvariant Ω
  classical : ∀ L ∈ Ω, ∃ z : G, IsClassicalMemberU t L z
  omega4 : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J →
    padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 → ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J)
  omega5 : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J → ∀ z : G, IsUniqueInvolution K z → ∀ v ∈ J,
    (¬ ∀ w ∈ J, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
      v ∈ Subgroup.normalizer (K : Set G)

theorem hypOmegaModU_iff_hypOmegaMod {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} : HypOmegaModU (.sl2 p f) Ω ↔ HypOmegaMod p f Ω := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at hq
    · exact hf
  refine ⟨fun h => ⟨h.conjInvariant, fun L hL => ?_, h.omega4, h.omega5⟩,
    fun h => ⟨h.conjInvariant, fun L hL => ?_, h.omega4, h.omega5⟩⟩
  · obtain ⟨z, hz⟩ := h.classical L hL
    exact ⟨z, hz.toGeneric hq⟩
  · obtain ⟨z, hz⟩ := h.classical L hL
    exact ⟨z, IsClassicalMemberU.ofGeneric hp2 hf hz⟩

variable {t : MemberType} [Finite G] {K₀ : Subgroup G} {z₀ : G}

theorem hypOmegaModU_conjClass (hc : t.Cert) (h₀ : IsClassicalMemberU t K₀ z₀)
    (hint : IsIntrinsicU t K₀ z₀)
    (h5 : AscHypOmega.Omega5At (Generic.CoreAssembly.conjClass K₀) K₀ z₀) :
    HypOmegaModU t (Generic.CoreAssembly.conjClass K₀) where
  conjInvariant := conjInvariant_conjClass K₀
  classical := by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, h₀.conj g⟩
  omega4 K hK J hJ hne := omega4_of_memberU hc h₀ hint hK hJ hne
  omega5 := omega5_of_omega5AtU hc h₀ h5

end HypOmega

section Induction


end Induction

section Stand


end Stand

end CFSG.ClassicalInvolution.Uniform
