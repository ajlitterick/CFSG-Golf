module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyAssembly
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyResidual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddClassical
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyPrimeSquare
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddRankTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddRankOne
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddRankOneGlue
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Component
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Graph
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyAltLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiComponent
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassicalProp
public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PureSemilinear

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.QuasithinUnique.Setup.X35

theorem familyTop
    (hlayer : ActorLayerProp) (hT : ActorComponentTransfer)
    (hTrans : X1.ComponentTransferProp) (hSec : X1.IrreducibleSectionProp)
    (hspor : NoSporadicComponentProp) (hsec : SectionProductionProp)
    (hlin3 : PrimeLinearThreeExclusionProp)
    (huni3 : PrimeUnitaryThreeExclusionProp) : OneQuasisimpleResidualProp := by
  have hGL3 : NoGL3ComponentProp := noGL3Component hlayer hT hTrans gl3GraphNormalizerExclusion
  have hA78 : NoAlt78BinaryLinearProp := noAlt78BinaryLinear hT hGL3
  have hSuz : NoSuzukiComponentProp := noSuzukiComponent hlayer hsec
  have hodd : OddClassicalSmallProp :=
    oddClassicalSmall CFSG.SectionRank.catalogStepHyp hlayer hTrans hSec hA78 hlin3 huni3
      primeSquareExclusion
  have hfam : FamilyRestrictionProp := familyRestriction hlayer hspor hSuz hA78 hodd
  exact oneQuasisimpleResidual hlayer hfam
    (componentOddRankTwoNormal CFSG.SectionRank.oddKernelCentralization
      CFSG.SectionRank.catalogStepHyp)
    oddRankOneOddClassical CFSG.QuasithinUnique.Vol2Native.EvenWit.oddRankOneEvenClassical
    oddRankOneChevalley oddRankOneReeTits trialityTwoHasRankTwo

end CFSG.QuasithinUnique.Setup.Family
