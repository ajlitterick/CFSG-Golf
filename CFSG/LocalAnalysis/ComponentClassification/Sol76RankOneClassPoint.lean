module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Tools

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

namespace RankOneClass

theorem exists_involution {K H : Subgroup G} (hK : IsTwoComponentIn K H) :
    ∃ b ∈ K, orderOf b = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card K := by
    by_contra h
    exact UnbalancedCorr.not_le_of_isPComponent_of_coprime hK.1 hK.2
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h) le_rfl
  obtain ⟨⟨b, hbK⟩, hb⟩ := exists_prime_orderOf_dvd_card' 2 h2
  exact ⟨b, hbK, by rwa [Subgroup.orderOf_mk] at hb⟩

theorem exists_central_involution {T : Subgroup G} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) :
    ∃ t ∈ T, orderOf t = 2 ∧ ∀ s ∈ T, s * t = t * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT
  have hZ : Nontrivial (center T) := hT2.center_nontrivial
  obtain ⟨n, hn0, hn⟩ := ((hT2.to_subgroup (center T)).nontrivial_iff_card).mp hZ
  have h2 : 2 ∣ Nat.card (center T) := hn ▸ dvd_pow_self 2 hn0.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center T) 2 h2
  refine ⟨((z : T) : G), (z : T).2, ?_, fun s hs => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  · exact congrArg Subtype.val (mem_center_iff.mp z.2 ⟨s, hs⟩)

theorem solomonLt_witness {K T : Subgroup G} (hK : IsSolomonMember K) (hT : T ≠ ⊥)
    (hT2 : IsPGroup 2 T) (hTQ : T ≤ coreActionKernel K)
    (hKT : IsTwoComponentIn (oddResidualIn (oddCoreIn (centralizer (T : Set G)) ⊔
      (K ⊓ centralizer (T : Set G)))) (centralizer (T : Set G))) :
    SolomonLt K (oddResidualIn (oddCoreIn (centralizer (T : Set G)) ⊔
      (K ⊓ centralizer (T : Set G)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKq := isQuasisimple_coreQuot_of_isSolomonMember hK
  obtain ⟨hRY, hLY, -, -⟩ :=
    cover_facts hKq inf_le_left (inf_centralizer_sup_oddCoreIn_eq hT2 hTQ)
  have hRL := twoLayer_inf_centralizer_le_of_witness hKq hT2 hTQ hKT
  have hRKT : twoLayerIn (K ⊓ centralizer (T : Set G)) ≤
      oddResidualIn (oddCoreIn (centralizer (T : Set G)) ⊔ (K ⊓ centralizer (T : Set G))) := by
    rw [hLY]
    exact oddResidualIn_mono le_sup_right
  have hRperf : ⁅twoLayerIn (K ⊓ centralizer (T : Set G)),
      twoLayerIn (K ⊓ centralizer (T : Set G))⁆ = twoLayerIn (K ⊓ centralizer (T : Set G)) := by
    rw [hLY]
    exact UnbalancedCorr.commutator_eq_of_isPComponent hRY.1 hRY.2
  have hRinv : ∃ b ∈ twoLayerIn (K ⊓ centralizer (T : Set G)), orderOf b = 2 := by
    rw [hLY]
    exact exists_involution hRY
  exact ⟨hK, isSolomonMember_of_isTwoComponentIn hT hT2 hKT, T, hT2, hTQ,
    isTwoComponentIn_conjClosure_of_not_le hKT hRL
      (not_le_coreActionKernel_of_le hRKT hRperf hRinv)⟩

end RankOneClass


end CFSG.ComponentClassification.Sol76
