module

public import CFSG.LocalAnalysis.ComponentClassification.BMCaseBabySchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic
public import CFSG.Monster.B.CTIB.OddCoreFree
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.StronglyEmbedded.ParityCriterion

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.BMCase

open CFSG.Monster.B CFSG.ComponentClassification.OuterAutomorphisms Subgroup

theorem generalizedFitting_eq_top_of_pinnedB {X : Type} [Group X] [Finite X]
    (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hnab : ∃ x y : CFSG.generalizedFitting X, x * y ≠ y * x)
    (hJ : Nonempty (CFSG.generalizedFitting X ≃* Blueprint.NativeSporadic.B)) :
    CFSG.generalizedFitting X = ⊤ := by
  have hC : centralizer (CFSG.generalizedFitting X : Set X) = ⊥ :=
    CFSG.ComponentClassification.CatalogueU.centralizer_generalizedFitting_eq_bot_of_simple hF
      hnab
  refine eq_top_iff.2 fun x _ => ?_
  have hFn : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  obtain ⟨f, hf⟩ := inner_of_mulEquiv_pinnedB _ hJ (MulAut.conjNormal x)
  have hcent : (f : X)⁻¹ * x ∈ centralizer (CFSG.generalizedFitting X : Set X) := by
    rw [mem_centralizer_iff]
    intro h hh
    have e := congrArg (fun β : MulAut (CFSG.generalizedFitting X) => (β ⟨h, hh⟩ : X)) hf
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, coe_mul, coe_inv] at e
    calc h * ((f : X)⁻¹ * x) = (f : X)⁻¹ * (f * h * (f : X)⁻¹) * x := by group
      _ = (f : X)⁻¹ * (x * h * x⁻¹) * x := by rw [e]
      _ = (f : X)⁻¹ * x * h := by group
  rw [hC, mem_bot, inv_mul_eq_one] at hcent
  rw [← hcent]
  exact f.2

theorem sporadicOddCoreFree_B : CatalogueU.SporadicOddCoreFree .B := by
  intro X _ _ hF hnab hJ t ht
  have htop := generalizedFitting_eq_top_of_pinnedB hF hnab hJ
  obtain ⟨ψ⟩ := hJ
  obtain ⟨ι⟩ := nonempty_pinnedB_equiv_Cbar
  have e : X ≃* Cbar :=
    ((Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans ψ).trans ι
  have h := CTIB.native_B_all_involution_centralizers_odd_core_free.2.1 (e t)
    ((MulEquiv.orderOf_eq e t).trans ht)
  exact CTIB.oddCore_eq_bot_of_equiv (CTIB.centralizerEquiv e t).symm h

end CFSG.ComponentClassification.BMCase
