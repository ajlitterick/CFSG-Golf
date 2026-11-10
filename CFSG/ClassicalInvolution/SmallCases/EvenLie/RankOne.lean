module

public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Basic
public import CFSG.Blueprint.Catalog
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.StronglyEmbedded.BenderBorelTransport
import CFSG.Adapters.LinearFieldTransport
import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
import CFSG.LieType.BorelTits.Suzuki
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups


theorem noNonsolvableClassical_of_suzukiModel {X : Type} [Group X] {f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel X 2 f) : NoNonsolvableClassical X := by
  obtain ⟨-, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := h
  have e' := e.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
    (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))
  have hX : Finite X := Finite.of_equiv ↥(CFSG.Blueprint.suzukiGroup a K) e.symm.toEquiv
  have : Finite (Sz a) := Finite.of_equiv X e'.toEquiv
  exact NoNonsolvableClassical.of_mulEquiv e'
    (NoNonsolvableClassical.of_fusionBenderBorel (bender_suzuki_borel_full a ha))

end CFSG.ClassicalInvolution
