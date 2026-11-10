module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryCover
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)

namespace UnitaryLevi

theorem _root_.CFSG.AGLEmbedding.CompParab.exists_sylow_normalizer_le {Y : Type} [Group Y]
    [Finite Y] {L J : Subgroup Y} (h : CompParab L J) :
    ∃ T : Sylow 2 ↥L,
      Subgroup.normalizer ((T : Subgroup ↥L) : Set ↥L) ≤ J.subgroupOf L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJL, T, ⟨hTL, hT2, hTi⟩, hNJ⟩ := h.parab
  let T' : Sylow 2 ↥L := (hT2.comap_subtype (K := L)).toSylow hTi
  refine ⟨T', fun x hx => ?_⟩
  rw [Subgroup.mem_subgroupOf]
  refine hNJ ⟨x.2, Subgroup.mem_normalizer_fintype fun t ht => ?_⟩
  have h1 : (⟨t, hTL ht⟩ : ↥L) ∈ (T' : Subgroup ↥L) := by
    simpa [T', Subgroup.mem_subgroupOf] using ht
  have h2 := (Subgroup.mem_normalizer_iff.1 hx ⟨t, hTL ht⟩).1 h1
  simpa [T', Subgroup.mem_subgroupOf] using h2

theorem exists_sylow_map_eq {G X : Type*} [Group G] [Group X] [Finite G] {ψ : G →* X}
    (hψ : Function.Surjective ψ) (T : Sylow 2 X) :
    ∃ S : Sylow 2 G, (S : Subgroup G).map ψ = (T : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective (p := 2) hψ T
  exact ⟨S, by rw [← hS, Sylow.coe_mapSurjective]⟩

theorem exists_sylow_normalizer_le_comap {G X : Type*} [Group G] [Group X] [Finite G]
    {ψ : G →* X} (hψ : Function.Surjective ψ) {J : Subgroup X} (T : Sylow 2 X)
    (hNJ : Subgroup.normalizer ((T : Subgroup X) : Set X) ≤ J) :
    ∃ S : Sylow 2 G, Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ J.comap ψ := by
  obtain ⟨S, hS⟩ := exists_sylow_map_eq hψ T
  refine ⟨S, fun x hx => ?_⟩
  rw [Subgroup.mem_comap]
  refine hNJ ?_
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [← hS]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨x * s * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx s).1 hs, by simp⟩
  · rintro ⟨s, hs, hsy⟩
    refine ⟨x⁻¹ * s * x, ?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.1 hx (x⁻¹ * s * x)).2
      have h2 : x * (x⁻¹ * s * x) * x⁻¹ = s := by group
      rw [h2] at h1
      exact h1 hs
    · simp [hsy, mul_assoc]


end UnitaryLevi

end CFSG.AGLEmbedding
