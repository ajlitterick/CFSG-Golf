module

public import CFSG.ClassicalInvolution.Asc77.AscSix69

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem exists_member_of_mem_USet' {U : Subgroup G} (hU : U ∈ USet Ω) :
    ∃ J ∈ Ω, U ≤ J := by
  obtain ⟨R, hR, hUR, -, -⟩ := hU
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  exact ⟨J, hJ, hUR.trans hRJ.1⟩


end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
