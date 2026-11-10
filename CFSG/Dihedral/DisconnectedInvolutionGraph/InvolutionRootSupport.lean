module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneInvolutions
public import CFSG.Dihedral.DisconnectedInvolutionGraph.InducedSupportedFunction

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem involution_zpowers_members (involution : Involution G) (element : G)
    (hmem : element ∈ Subgroup.zpowers (involution : G)) :
    element = 1 ∨ element = (involution : G) := by
  classical
  obtain ⟨exponent, hexponent, hequal⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp hmem)
  have hbound : exponent < 2 := by simpa only [Finset.mem_range, involution.property] using hexponent
  have hcases : exponent = 0 ∨ exponent = 1 := by omega
  rcases hcases with rfl | rfl
  · exact Or.inl (by simpa only [pow_zero] using hequal.symm)
  · exact Or.inr (by simpa only [pow_one] using hequal.symm)

theorem involution_zpowers_normalizer_eq_centralizer (involution : Involution G) :
    Subgroup.normalizer (Subgroup.zpowers (involution : G) : Set G) =
      Subgroup.centralizer ({(involution : G)} : Set G) := by
  apply le_antisymm
  · intro actor hactor
    have hmem := (Subgroup.mem_normalizer_iff.mp hactor (involution : G)).mp
      (Subgroup.mem_zpowers (involution : G))
    rcases involution_zpowers_members involution _ hmem with hone | hequal
    · have hinvolution : (involution : G) = 1 := by
        have heq := congrArg (fun element => actor⁻¹ * element * actor) hone
        calc
          (involution : G) = actor⁻¹ * (actor * (involution : G) * actor⁻¹) * actor := by group
          _ = 1 := by simpa only [mul_one, inv_mul_cancel] using heq
      have horder := involution.property
      rw [hinvolution, orderOf_one] at horder
      omega
    · apply Subgroup.mem_centralizer_singleton_iff.mpr
      have heq := congrArg (fun element => element * actor) hequal
      simpa only [inv_mul_cancel_right] using heq
  · intro actor hactor
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro element hmem
    obtain ⟨exponent, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hcommute : Commute actor (involution : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hactor
    exact (hcommute.zpow_right exponent).symm.eq


end CFSG.DisconnectedInvolutionGraph.Helpers
