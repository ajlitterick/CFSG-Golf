module

public import CFSG.LocalAnalysis.StandardType.GGHypSixTypeA
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Families

theorem ggRootDetect_of_rank_lt {t : StatedLieTag} (h : ∀ n f, (ggU t n f).D.rank < 2) :
    GGRootDetect t := by
  intro G _ _ n f ψ _ hrk
  exact absurd hrk (Nat.not_le.mpr (h n f))

theorem ggRootDetect_pOmegaOdd : GGRootDetect .POmegaOdd := by
  intro G _ _ n f ψ hadm
  exact absurd rfl hadm.2.2.2

@[expose] def GGRootDetectRest : Prop :=
  GGRootDetect .PSU ∧ GGRootDetect .PSp ∧ GGRootDetect .POmegaPlus ∧
    GGRootDetect .POmegaMinus ∧ GGRootDetect .F4 ∧ GGRootDetect .E6 ∧ GGRootDetect .E7 ∧
    GGRootDetect .E8 ∧ GGRootDetect .twistedE6

theorem ggRootDetect_all (h : GGRootDetectRest) : ∀ t, GGRootDetect t := by
  obtain ⟨hU, hSp, hP, hM, hF4, hE6, hE7, hE8, h2E6⟩ := h
  intro t
  cases t
  · exact ggRootDetect_psl
  · exact hU
  · exact hSp
  · exact ggRootDetect_pOmegaOdd
  · exact hP
  · exact hM
  · exact ggRootDetect_of_rank_lt fun _ _ => Nat.zero_lt_two
  · exact hF4
  · exact hE6
  · exact hE7
  · exact hE8
  · exact h2E6
  · exact ggRootDetect_of_rank_lt fun _ _ => Nat.zero_lt_two
  · exact ggRootDetect_of_rank_lt fun _ _ => Nat.zero_lt_two
  · exact ggRootDetect_of_rank_lt fun _ _ => Nat.zero_lt_two
  · exact ggRootDetect_of_rank_lt fun _ _ => Nat.zero_lt_two
  · exact ggRootDetect_of_rank_lt fun _ _ => Nat.zero_lt_two


end Families

section Assembly


end Assembly

end CFSG.StandardType
