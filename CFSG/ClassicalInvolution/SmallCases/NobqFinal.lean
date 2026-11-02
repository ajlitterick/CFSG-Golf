module

public import CFSG.ClassicalInvolution.SmallCases.NobqSmall
public import CFSG.ClassicalInvolution.SmallCases.NobqSporadic
public import CFSG.ClassicalInvolution.SmallCases.NobqLy
public import CFSG.ClassicalInvolution.SmallCases.NobqA7
public import CFSG.ClassicalInvolution.SmallCases.NobqAlt
public import CFSG.ClassicalInvolution.SmallCases.NobqL2
public import CFSG.ClassicalInvolution.SmallCases.NobqSz
public import CFSG.ClassicalInvolution.SmallCases.NobqU3
public import CFSG.ClassicalInvolution.SmallCases.NobqL34
public import CFSG.Certificates.CosetTableShort
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Ly
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyCert
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinConvention
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISymplectic
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.ComponentClassification.OuterAutomorphisms

structure SmallRemainingFacts : Prop where
  ly_out : Nat.card (Outer NativeSporadic.Ly) = 1

theorem noDatum_Ly (hOut : Nat.card (Outer NativeSporadic.Ly) = 1) (F : Type) [Group F]
    (h : NativeSporadic.IsSporadic F .Ly) : NoDatum F := by
  obtain ⟨e⟩ := h
  have : Finite NativeSporadic.Ly := Finite.of_equiv _ CFSG.Sporadic.Ly.lyEquivJ.symm.toEquiv
  exact NoDatum.of_mulEquiv e (noDatum_of_noUniqueInvNormal noUniqueInvNormal_Ly
    (OutTwoCyclic.of_card_le_two (F := NativeSporadic.Ly) (by rw [hOut]; norm_num)))

theorem SmallRemainingFacts.smallNoDatum (h : SmallRemainingFacts) : SmallNoDatum where
  a7 := noDatum_alternating_seven
  psu34 := noDatum_of_statedPSU
  psl28 := fun F _ hF => noDatum_of_lieModel_psl_two_even F hF
  psl216 := fun F _ hF => noDatum_of_lieModel_psl_two_even F hF
  psl34 := fun F _ hF => noDatum_of_lieModel_psl_three_two F hF
  sz8 := fun F _ hF => noDatum_of_lieModel_twistedB2 F hF
  alt := noDatum_alternating
  m22 := noDatum_M22
  m23 := noDatum_M23
  j1 := noDatum_J1
  j2 := noDatum_J2
  j3 := noDatum_J3
  mcl := noDatum_McL
  ly := noDatum_Ly h.ly_out

theorem normalOddByQuaternionSmall_of_remaining (hGH : GH74SectionalModels)
    (h : SmallRemainingFacts) :
    NormalOddByQuaternionUnder fun {G} _ _ _ => TwoSubgroupsFourGenerated (genFittingFStar G) :=
  normalOddByQuaternionSmall_of_gh74 hGH h.smallNoDatum

end CFSG.ClassicalInvolution.Nobq
