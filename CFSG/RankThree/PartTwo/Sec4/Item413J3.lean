module

public import CFSG.RankThree.PartTwo.Sec4.Item47Native
public import CFSG.RankThree.Asc83Table.J3
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.Blueprint

theorem rankJ3_holds :
    CFSG.pRank 3 (NativeSporadic.Carrier .J3 ⧸ Subgroup.center (NativeSporadic.Carrier .J3)) ≤
      3 := by
  have hZ : Subgroup.center (NativeSporadic.Carrier .J3) = ⊥ :=
    center_carrier_eq_bot_of_cover (s := .J3) (by simp [sporadicCovers46])
  rw [CFSG.RankThree.Asc83Table.pRank_congr
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)]
  exact CFSG.RankThree.Asc83Table.J3.native_J3.1.le

end CFSG.RankThree.PartTwo.Sec4
