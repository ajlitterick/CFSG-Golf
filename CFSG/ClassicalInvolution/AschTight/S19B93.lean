module

public import CFSG.ClassicalInvolution.AschTight.S19BC11

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjSub_mem_USet {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) (g : G) : conjSub g U ∈ USet Ω := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  refine ⟨conjSub g R, mem_RSet_of_isSylow2In (hΩ g J hJ) (hRJ.conj g), conjSub_mono hUR,
    isCyclic_conjSub hcyc g, ?_⟩
  rw [conjSub, conjSub, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact hidx


end CFSG.ClassicalInvolution.Disconnected.AschTight.S19B
