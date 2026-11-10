module

public import CFSG.Sporadic.Schreier.J4SReal
public import CFSG.Sporadic.Schreier.J4SEleven
public import CFSG.Sporadic.Schreier.J4SCentGen

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem rowLin_sub_one_eq (h : J) :
    ((rowLin h : (Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2)) :
      (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) - LinearMap.id =
      Matrix.mulVecLin (φ h⁻¹ - 1)ᵀ := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.sub_apply, LinearEquiv.coe_coe, rowLin_apply, LinearMap.id_apply,
    Matrix.mulVecLin_apply, Matrix.mulVec_transpose, Matrix.vecMul_sub, Matrix.vecMul_one, φ_apply,
    Subgroup.coe_inv]

theorem rank_rowLin_sub_one (h : J) :
    Module.finrank (ZMod 2) (LinearMap.range
      (((rowLin h : (Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2)) :
        (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) - LinearMap.id)) =
      (φ h⁻¹ - 1).rank := by
  rw [rowLin_sub_one_eq, ← Matrix.rank_transpose (φ h⁻¹ - 1)]
  rfl

theorem small_rank_rowGroup :
    ∀ g ∈ rowGroup, (orderOf g = 2 ∨ orderOf g = 3) →
    3 ≤ Module.finrank (ZMod 2) (LinearMap.range
      ((g : (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) - LinearMap.id)) := by
  rintro _ ⟨h, rfl⟩ ho
  rw [rank_rowLin_sub_one]
  have hoh : orderOf h⁻¹ = orderOf (rowLin h) := by
    rw [orderOf_inv, orderOf_injective rowLin rowLin_injective h]
  have h3 := R3E_J4_elements_of_order_two_or_three_have_rank_at_least_three h⁻¹ (hoh ▸ ho)
  rwa [← φ_apply] at h3

theorem ker_rowLin_qz : LinearMap.ker
    (((rowLin qz : (Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2)) :
      (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) - 1) = rowFix (φ qz) := by
  ext v
  rw [LinearMap.mem_ker, mem_rowFix, LinearMap.sub_apply, LinearEquiv.coe_coe, rowLin_apply,
    Module.End.one_apply, sub_eq_zero]
  have e1 : (((qz : GL (Fin 112) (ZMod 2))⁻¹ : GL (Fin 112) (ZMod 2)) :
      Matrix (Fin 112) (Fin 112) (ZMod 2)) * φ qz = 1 := by
    rw [φ_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e2 : φ qz * (((qz : GL (Fin 112) (ZMod 2))⁻¹ : GL (Fin 112) (ZMod 2)) :
      Matrix (Fin 112) (Fin 112) (ZMod 2)) = 1 := by
    rw [φ_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  constructor
  · intro h
    calc v ᵥ* φ qz = (v ᵥ* (((qz : GL (Fin 112) (ZMod 2))⁻¹ : GL (Fin 112) (ZMod 2)) :
          Matrix (Fin 112) (Fin 112) (ZMod 2))) ᵥ* φ qz := by rw [h]
      _ = v := by rw [Matrix.vecMul_vecMul, e1, Matrix.vecMul_one]
  · intro h
    calc v ᵥ* (((qz : GL (Fin 112) (ZMod 2))⁻¹ : GL (Fin 112) (ZMod 2)) :
          Matrix (Fin 112) (Fin 112) (ZMod 2)) =
        (v ᵥ* φ qz) ᵥ* (((qz : GL (Fin 112) (ZMod 2))⁻¹ : GL (Fin 112) (ZMod 2)) :
          Matrix (Fin 112) (Fin 112) (ZMod 2)) := by rw [h]
      _ = v := by rw [Matrix.vecMul_vecMul, e2, Matrix.vecMul_one]

theorem finrank_ker_rowLin_qz :
    Module.finrank (ZMod 2) (LinearMap.ker
    (((rowLin qz : (Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2)) :
      (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) - 1)) = 2 := by
  rw [ker_rowLin_qz, finrank_rowFix_qz]

theorem closure_Q11_gens :
    Subgroup.closure ({⟨qx, qx_mem⟩, ⟨qy, qy_mem⟩} : Set Q11) = ⊤ := by
  apply Subgroup.map_injective Q11.subtype_injective
  rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  show Subgroup.closure ({qx, qy} : Set J) = Q11
  rfl

theorem qz_eq_commutator :
    (⟨qz, qz_mem⟩ : Q11) = ⁅(⟨qx, qx_mem⟩ : Q11), ⟨qy, qy_mem⟩⁆ := Subtype.ext rfl

theorem odd_card_pointwiseFixingAut_Q11 :
    Odd (Nat.card (pointwiseFixingAut Q11)) :=
  @odd_card_pointwiseFixingAut_of_realization (Fin 112 → ZMod 2) _ _ J (Subgroup.toGroup J) _ _
    jq jq_nondegenerate rowLin rowLin_injective rowGroup_le_orthogonal small_rank_rowGroup
    isoHom isoHom_injective isoHom_mem rowLin_aut Q11 isExtraspecial_Q11 card_Q11 exponent_Q11
    ⟨qx, qx_mem⟩ ⟨qy, qy_mem⟩ ⟨qz, qz_mem⟩ closure_Q11_gens qz_eq_commutator
    (Module.finrank_fin_fun (ZMod 2)) finrank_ker_rowLin_qz


end CFSG.Sporadic.J4Schreier
