module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexUnitAffine
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NormalGraphFusion
public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII

universe v

variable {G : Type v} [Group G]

@[expose, instance_reducible] def unitAffineAction (U : Subgroup G) :
    MulAction (unitAffineGroup U) U :=
  MulAction.compHom U (unitAffinePerm U)

@[expose, instance_reducible] def unitCoordinateAction (U : Subgroup G) (u : G) :
    MulAction (Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) U :=
  MulAction.compHom U (unitCoordinatePerm U u)

theorem unitAffineHom_action (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x)
    (n : Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) (x : U) :
    unitAffinePerm U (unitAffineHom U u hu hcentral n) x = unitCoordinatePerm U u n x := by
  exact congrArg (fun f => f n x) (unitAffinePerm_comp_unitAffineHom U u hu hcentral)

theorem unitTranslateEquiv_unitCoordinatePerm (U : Subgroup G) (u : G)
    (n : Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) (x : U) :
    unitTranslateEquiv U u (unitCoordinatePerm U u n x) =
      cosetNormalizerPerm ((fun x : G => u * x) '' (U : Set G)) n
        (unitTranslateEquiv U u x) := by
  apply Subtype.ext
  rw [unitTranslateEquiv_apply, unitCoordinatePerm_apply, cosetNormalizerPerm_apply,
    unitTranslateEquiv_apply, mul_inv_cancel_left]


end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
