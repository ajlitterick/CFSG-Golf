module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CoverTransport

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding
open CFSG.AGLEmbedding.UnitaryLevi

theorem exists_sylow_normalizer_le_of_parabolic {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (h : IsParabolicTwo L J) :
    ∃ T : Sylow 2 ↥L, Subgroup.normalizer ((T : Subgroup ↥L) : Set ↥L) ≤ J.subgroupOf L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJL, T, ⟨hTL, hT2, hTi⟩, hNJ⟩ := h
  let T' : Sylow 2 ↥L := (hT2.comap_subtype (K := L)).toSylow hTi
  refine ⟨T', fun x hx => ?_⟩
  rw [Subgroup.mem_subgroupOf]
  refine hNJ ⟨x.2, Subgroup.mem_normalizer_fintype fun t ht => ?_⟩
  have h1 : (⟨t, hTL ht⟩ : ↥L) ∈ (T' : Subgroup ↥L) := by
    simpa [T', Subgroup.mem_subgroupOf] using ht
  have h2 := (Subgroup.mem_normalizer_iff.1 hx ⟨t, hTL ht⟩).1 h1
  simpa [T', Subgroup.mem_subgroupOf] using h2


end CFSG.HardMathSupport.Curtis.UnitaryLevi
