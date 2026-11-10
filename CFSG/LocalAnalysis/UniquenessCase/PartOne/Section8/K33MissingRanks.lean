module

public import CFSG.GroupTheory.WeirSylow.CrossRankLinear
public import CFSG.GroupTheory.WeirSylow.CrossRankUnitary
public import CFSG.HardMathSupport.Lang.Proving.FieldCubeRoots
public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.NormalForm
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TT1061
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.PSUFour
public import CFSG.Quasithin.EmptyFaithful.R3c3Rank
public import CFSG.Quasithin.H13.KGFactLieOutAbL
public import CFSG.RankThree.PartOne.LIT.RankProjective
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open CFSG.Blueprint Subgroup

variable {X : Type} [Group X] [Finite X]


theorem pRank_three_eq_two_of_lieModel_PSU_five_of_mod_one {p f : ℕ}
    (hq3 : p ^ f % 3 = 1) (h : LieModel X .PSU 5 p f) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  have hC : StatedClassicalModel X .PSU 5 p f := h.statedClassicalModel (by decide)
  obtain ⟨hadm, K, hKfield, hKfin, hK, ⟨e⟩⟩ := hC
  letI := hKfield
  letI := hKfin
  have hf : 1 ≤ f := hadm.2.1
  have h3q : 3 ∣ p ^ f - 1 := by
    refine ⟨p ^ f / 3, ?_⟩
    have hdm := Nat.div_add_mod (p ^ f) 3
    omega
  have hp3 : p ≠ 3 := by
    intro hp
    subst hp
    have h3dvd : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega : f ≠ 0)
    have h1 : 3 ∣ 3 ^ f - (3 ^ f - 1) := Nat.dvd_sub h3dvd h3q
    have hge : 1 ≤ 3 ^ f := Nat.one_le_pow f 3 (by norm_num)
    rw [show 3 ^ f - (3 ^ f - 1) = 1 by omega] at h1
    omega
  refine le_antisymm ?_ ?_
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    have hle := CFSG.GroupTheory.WeirSylow.pRank_top_statedProj_statedSU_le_div_two
      (p := 3) (hp := by decide) (L := K) (q := p ^ f) (n := 5) hK (by norm_num) h3q
    simpa using hle
  · exact CFSG.HardMathSupport.Timmesfeld.FieldBonus.two_le_pRank_three_psu_four
      (n := 5) (by norm_num) hp3 (h.statedClassicalModel (by decide))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
