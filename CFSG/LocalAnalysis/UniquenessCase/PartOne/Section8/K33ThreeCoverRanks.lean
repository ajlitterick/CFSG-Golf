module

public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreThree
public import CFSG.LocalAnalysis.UniquenessCase.Lie.Cover
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd
public import CFSG.RankThree.PartTwo.Census.Carrier.TitsCert
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcTits
public import CFSG.Sporadic.Schreier.J1QT

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG CFSG.Open CFSG.Blueprint Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UCK

variable {X : Type} [Group X] [Finite X]


theorem pRank_three_eq_two_of_lieModel_Tits
    (h : LieModel X .Tits 0 2 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  have hTits : ReeTitsModel X .Tits 2 1 := (h.reeTitsModel (by decide)).2
  have hlow : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Census.two_le_pRank_three_of_titsModel hTits
  have hupper : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 := by
    obtain ⟨K, hKfield, hKfin, hKchar, hK2, ⟨e⟩⟩ :=
      CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model hTits
    letI := hKfield
    letI := hKfin
    letI := hKchar
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    have hΓ : CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.LieType.Ree.reeFixed
        CFSG.LieType.Ree.ReeTag.F4 K 0)) ≤ 2 := by
      rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3
          (⊤ : Subgroup (CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0)),
        CFSG.SectionRank.pRank_coe_eq_assemblyPRank 3
          (⊤ : Subgroup (CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0))]
      exact CFSG.RankThree.PartTwo.Census.Carrier.Tits.pRank_three_reeFixed hK2
    exact (CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num)
      (commutator (CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0)).subtype
      (commutator (CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0)).subtype_injective).trans
      hΓ
  exact le_antisymm hupper hlow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
