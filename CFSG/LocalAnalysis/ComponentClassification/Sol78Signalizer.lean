module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78Main
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic
public import CFSG.Sporadic.SmallOddCore.HSMcL
public import CFSG.Sporadic.Schreier.LyOddCoreFree
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyFixedSet
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X] [IsSimpleGroup X]

noncomputable def cfsgGeneralizedFittingEquiv (hnonab : ∃ a b : X, a * b ≠ b * a) :
    CFSG.generalizedFitting X ≃* X :=
  (MulEquiv.subgroupCongr ((CFSG.generalizedFitting_eq_componentClassification X).trans
    (SmallLocal.simple_generalized_fitting_self_local X hnonab).2.2.2.2)).trans
    Subgroup.topEquiv

theorem false_of_mulEquiv_sporadic {s : TauCeti.SporadicName}
    (hs : CatalogueU.SporadicOddCoreFree s) (hnonab : ∃ a b : X, a * b ≠ b * a)
    (e : X ≃* Blueprint.NativeSporadic.Carrier s)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) : False := by
  let eF := cfsgGeneralizedFittingEquiv hnonab
  have hFnonab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨eF.symm a, eF.symm b, fun h => hab (by simpa using congrArg eF h)⟩
  obtain ⟨z, hz2, hzc⟩ := hz
  exact hzc (hs X eF.isSimpleGroup hFnonab ⟨eF.trans e⟩ z hz2)

theorem solomonSignalizer_of_inputs (h2An : GSThmB.Solomon2AnInput)
    (hCI : GSLit.ClassicalInvolutionInput) (hS : SchreierFor Blueprint.Catalog)
    (hSchur : SolAltLit.SchurAlternatingMultiplierInput) (hHe : TBLit.HeldTrivialMultiplier)
    (hPump : AlternatingPumpUpInput) : GSThmB.SolomonSignalizerInput := by
  intro X _ _ _ hnonab hK hz hU b n K hb hn hn7 hKb hKc hKe
  by_contra hne
  obtain ⟨e⟩ := hKe
  have hspor : ¬ (Nonempty (X ≃* Blueprint.NativeSporadic.M11) ∨
      Nonempty (X ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (X ≃* Blueprint.NativeSporadic.Ly)) := by
    rintro (⟨⟨eM⟩⟩ | ⟨⟨eM⟩⟩ | ⟨⟨eM⟩⟩)
    · exact false_of_mulEquiv_sporadic (s := .M11) CatalogueU.sporadicOddCoreFree_M11 hnonab eM
        hz
    · exact false_of_mulEquiv_sporadic (s := .McL)
        (fun _ _ _ hF _ hJ t ht =>
          Sporadic.SmallOddCore.ctu_catalog_hs_mcl_almost_simple_odd_core_vanishing hF (.inr hJ)
            t ht) hnonab eM hz
    · exact false_of_mulEquiv_sporadic (s := .Ly) Sporadic.LySchreier.sporadicOddCoreFree_Ly
        hnonab eM hz
  exact not_isDoublePair h2An hCI hS hSchur hHe hPump hnonab hK hU hspor b K n
    ⟨hb, hKb, hKc, hn, hn7, hne, ⟨e⟩⟩

end CFSG.ComponentClassification.Sol78
