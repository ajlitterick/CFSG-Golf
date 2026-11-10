module

public import CFSG.Quasithin.Background.C35InspSp4
public import CFSG.Quasithin.Background.C35InspG2
public import CFSG.Quasithin.Background.C35InspF4
public import CFSG.Quasithin.Background.C35InspA8E
public import CFSG.Quasithin.Background.C35InspLeviAll
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.Sporadic.He
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central

public section

namespace CFSG.Quasithin.C35Pf

theorem inspC35_holds :
    InspC35 :=
  ⟨small_holds, l3_holds, sp4_holds, g2_holds, d4_holds, f4_holds, l45_holds, a8cover_holds,
    C35Levi.levi_holds⟩

end CFSG.Quasithin.C35Pf
