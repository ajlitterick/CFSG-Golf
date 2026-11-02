module

public import CFSG.RankThree.PartOne.KP.CoverEmbedding
public import CFSG.RankThree.PartOne.KP.BData
public import CFSG.Monster.B.CTIB.UniqueComponent
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Monster.B CFSG.Monster.B.CTIB CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
open CFSG.LieType.Chevalley.C2E6Std
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem exists_quasisimple_in_centralizer_labelS :
    ∃ K : Subgroup (Subgroup.centralizer ({labelS} : Set Sbp)), IsQuasisimple K ∧
      Nat.card (Subgroup.center K) = 2 ∧ Nonempty (K ⧸ Subgroup.center K ≃* stdGroup) := by
  obtain ⟨-, hperf, -, hcen, hc2, ⟨θ⟩, -, hcard⟩ := derivedCoverInput_holds
  have hs' := @MulEquiv.isSimpleGroup _ _ _ _ stdGroup_simple θ
  have hq := isQuasisimple_of_cover hperf hcen hc2 hs' (by rw [hcard]; norm_num)
  have hz := card_center_commutator hcen hc2
  obtain ⟨ι, hι⟩ := exists_embedding_into_centralizer Shat Eam Eam_le_Shat sEquiv labelS cS
    sEquiv_labelS (fun x hx => Subgroup.mem_centralizer_singleton_iff.1 (Eam_le_centralizer hx))
  exact exists_quasisimple_range_of_injective (ι.comp (commutator Eam).subtype)
    (hι.comp (commutator Eam).subtype_injective) hq hz
    ((QuotientGroup.quotientMulEquivOfEq (center_commutator_eq hcen)).trans θ)

theorem bMonsterData_Sbp : BMonsterData Sbp := by
  obtain ⟨K, hq, hz, hQ⟩ := exists_quasisimple_in_centralizer_labelS
  exact ⟨labelS, K, hq, hz, hQ⟩

theorem sectionsForceEvenRankFour_B : SectionsForceEvenRankFour (Carrier .B) :=
  sectionsForceEvenRankFour_B_of_monsterData iotaEquiv bMonsterData_Sbp

end CFSG.RankThree.PartOne
