module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLBalance
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma410
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitRankOneBranch
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitOddCoreReduction
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitOuterReduction
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSkeleton
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Cover
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3CheckInputs
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Ly
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyCert
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Pattern
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLSide
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OneComp
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Choice
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSporadic
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISymplectic
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.RankThree.PartOne.LIT.RankMatrix
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.W2Lemma26A

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG

theorem footeInitialReductions_of_known_inputs
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) : FooteInitialReductions :=
  footeInitialReductions_of_lBalance footeLBalanceInput_holds hCI hGA hGC hSA

theorem footeRankBound_of_known_inputs_lb
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (hSol : Sol76T13.SolomonThm13Simple)
    (hM3 : FooteSolomonFamilyInput) (h47 : FooteThm47Statement)
    (hAsc : Foote5.AschbacherCentralCoreInput) (h2An : GSThmB.Solomon2AnInput) : FooteRankBound :=
  footeRankBound_of_known_inputs_410 footeLBalanceInput_holds hCI hGA hSA hSol hM3 h47 hAsc h2An

theorem footeGeneralStatement_of_known_inputs
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (hSol : Sol76T13.SolomonThm13Simple)
    (hM3 : FooteSolomonFamilyInput) (h47 : FooteThm47Statement)
    (hAsc : Foote5.AschbacherCentralCoreInput) (h2An : GSThmB.Solomon2AnInput)
    (h5 : FooteRankTwoExclusion) : FooteGeneralStatement :=
  footeGeneralStatement_of_steps (footeInitialReductions_of_known_inputs hCI hGA hGC hSA)
    (footeRankBound_of_known_inputs_lb hCI hGA hSA hSol hM3 h47 hAsc h2An) h5

theorem footeMaximalInput_of_known_inputs
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (hSol : Sol76T13.SolomonThm13Simple)
    (hM3 : FooteSolomonFamilyInput) (h47 : FooteThm47Statement)
    (hAsc : Foote5.AschbacherCentralCoreInput) (h2An : GSThmB.Solomon2AnInput)
    (h5 : FooteRankTwoExclusion)
    (hcore : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
      Assembly.KProper Blueprint.Catalog X → FooteCoreHypothesis X) :
    FooteMaximalInput :=
  footeMaximalInput_of_general
    (footeGeneralStatement_of_known_inputs hCI hGA hGC hSA hSol hM3 h47 hAsc h2An h5) hcore

end CFSG.ComponentClassification.FooteLit
