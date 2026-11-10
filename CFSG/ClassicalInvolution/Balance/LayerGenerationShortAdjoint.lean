module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationSimpleParam
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ClassicalInvolution.ModelFacts (subgroupOf_rootSubgroup_sup_eq)
open CFSG.LieType.Steinberg.Adjoint
  (xPar rootGroup f4Datum f4Par xPar_of_isRoot xPar_injective xPar_zero)

section Generic

variable {τ : Tag} {K : Type} [Field K]


end Generic

section Component

variable {τ : Tag} {K : Type} [Field K] [Finite K]


end Component

section F4

variable {τ : Tag} {K : Type} [Field K]

theorem coe_xPar_eq_pinnedX {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : K) :
    ((xPar (rootOperatorFamily τ) γ c : adjointGroup τ K) : ModGL τ K) =
      pinnedX τ K γ (((rootOperatorFamily τ).pinnedFamilySign γ : ℤ) * c) := by
  have h := (rootOperatorFamily τ).pinnedX_eq_eltUnit K hγ
    (((rootOperatorFamily τ).pinnedFamilySign γ : K) * c)
  rw [← mul_assoc, (rootOperatorFamily τ).pinnedFamilySign_mul_self K γ, one_mul] at h
  rw [xPar_of_isRoot hγ, h]
  rfl

theorem rootDiagAut_xPar (a : Fin τ.rank → Kˣ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : K) :
    rootDiagAut τ K a (xPar (rootOperatorFamily τ) γ c) =
      xPar (rootOperatorFamily τ) γ ((rootChar a γ : K) * c) := by
  apply Subtype.ext
  rw [coe_rootDiagAut, coe_xPar_eq_pinnedX hγ, coe_xPar_eq_pinnedX hγ,
    rootDiagUnit_conj_pinnedX a hγ]
  congr 1
  ring

theorem rootChar_single_eq (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    rootChar a (Pi.single i 1) = a i := by
  have := rootChar_nsmul_single a i 1
  rwa [one_smul, pow_one] at this

theorem rootChar_neg_eq_inv (a : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar a (-v) = (rootChar a v)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← rootChar_add, add_neg_cancel, rootChar_zero]


end F4

section Param


end Param

end CFSG.ClassicalInvolution.Balance
