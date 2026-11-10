module

public import CFSG.ClassicalInvolution.Balance.Theorem5Triangle
public import CFSG.ClassicalInvolution.Balance.BootstrapFinal
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Theorem5

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance.Bootstrap

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section P1

theorem localOddCentral_of_framesMeet [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) {x : G} (hx1 : x ≠ 1)
    (hmeet : ∀ K ∈ centMembers Ω x, ∃ A : Subgroup G, IsElemAbelian 2 A ∧ Nat.card A = 8 ∧
      (∀ Φ ∈ signalizerFunctorEk 2 2 A, deltaCore Φ = ⊥) ∧ x ∈ A ∧ ∃ L₀ ∈ Ω, ∃ z₀ ∈ A,
        IsClassicalMember p f L₀ z₀ ∧ L₀ ≤ Subgroup.centralizer (A : Set G) ∧
          InCommonComponent x K L₀) :
    LocalOddCentral Ω {x} := by
  intro d hd
  rw [Subgroup.mem_center_iff]
  intro y
  by_cases hne : (centMembers Ω x).Nonempty
  · have hgen := (inClass_local hΩ {x} hne).generated
    have hle : (⨆ L ∈ restrictFamily (centralizingMembers Ω {x}) (centralizingLayer Ω {x}), L) ≤
        Subgroup.centralizer ({d} : Set ↥(centralizingLayer Ω {x})) := by
      refine iSup₂_le fun L hL => ?_
      obtain ⟨K, hK, hKY, rfl⟩ := hL
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨A, hA, hcard, hΔ, hxA, L₀, hL₀Ω, z₀, hz₀A, hz₀, hL₀A, hcc⟩ := hmeet K hK
      exact Subtype.ext (member_commutes_oddCore_of_deltaCore_eq_bot hnab hp2 hq h0 hA1 hΩ hIH
        hA hcard hΔ hxA hx1 hK hL₀Ω hz₀ hz₀A hL₀A hcc d hd k
        (Subgroup.mem_subgroupOf.mp hk)).symm
    have hy : y ∈ (⨆ L ∈ restrictFamily (centralizingMembers Ω {x}) (centralizingLayer Ω {x}), L) :=
      hgen ▸ Subgroup.mem_top y
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  · have hY : centLayer Ω x = ⊥ := by
      refine le_bot_iff.mp (centLayer_le fun L hL => ?_)
      exact absurd ⟨L, hL⟩ hne
    have htriv : ∀ z : ↥(centLayer Ω x), z = 1 := fun z =>
      Subtype.ext (by
        have := z.2
        simpa only [hY, Subgroup.mem_bot, Subgroup.coe_one] using this)
    rw [htriv y, htriv d]

end P1

section Assembly


section P1Frames


end P1Frames


end Assembly

section BootTriple


@[expose] def TriangleConnectedAll (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        TriangleConnected p f (CoreAssembly.conjClass K)


@[expose] def TriangleLayers (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        ∀ A : Subgroup G, IndepTripleOn p f (CoreAssembly.conjClass K) A →
          ∀ a ∈ A, a ≠ 1 → ComponentLayersAt (CoreAssembly.conjClass K) A a


end BootTriple

end CFSG.ClassicalInvolution.Balance.Theorem5
