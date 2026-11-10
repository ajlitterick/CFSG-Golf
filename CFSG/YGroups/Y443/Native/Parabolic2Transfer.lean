module

public import CFSG.YGroups.Y443.Native.Parabolic2Conj
public import CFSG.YGroups.Y443.Tri.Parabolic2Eval

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short CFSG.Open

theorem armSwapL_eq : armSwapL = ρL := rfl

theorem y443RhoM_axL_armSwapL {s : ℕ} (hs : s ≤ 11) :
    y443RhoM.toMonoidHom (axL s) = axL (armSwapL s) := by
  show y443RhoM (axL s) = _
  rw [y443RhoM_axL hs, armSwapL_eq]

theorem fM_comp_rhoM :
    fM.comp y443RhoM.toMonoidHom = (MulAut.conj Grho).toMonoidHom.comp fM :=
  fM_comp_of_axL fun _ hs => y443RhoM_axL_armSwapL hs

theorem fM_rhoM
    (m : MonsterY443Derived) : fM (y443RhoM m) = Grho * fM m * Grho⁻¹ :=
  DFunLike.congr_fun fM_comp_rhoM m


theorem injOn_fM_H'_iff :
    Set.InjOn fM y443H' ↔ Set.InjOn fM y443H := by
  rw [← injOn_comp_rho_iff fM, fM_comp_rhoM]
  constructor
  · intro h a ha b hb hab
    exact h ha hb (by show (MulAut.conj Grho) (fM a) = (MulAut.conj Grho) (fM b); rw [hab])
  · intro h a ha b hb hab
    exact h ha hb ((MulAut.conj Grho).injective hab)

theorem y443H'_map_fM :
    y443H'.map fM = (y443H.map fM).map (MulAut.conj Grho).toMonoidHom := by
  rw [← y443H_map_comp_rho fM, fM_comp_rhoM, ← Subgroup.map_map]


theorem fM_y443C'_conj :
    fM y443C' = Grho * fM y443C * Grho⁻¹ := fM_rhoM y443C

theorem fM_y443X'_conj :
    fM y443X' = Grho * fM y443X * Grho⁻¹ := by
  rw [← y443RhoM_X]
  exact fM_rhoM y443X


theorem fM_y443C'_op_eq :
    ((fM y443C' : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = evalGL sletP := by
  rw [fM_y443C'_eq_evalGL, sletP, armSwapL_eq]


theorem fM_y443C_mul_y443C'_mem_shortClass :
    ((fM y443C : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * ((fM y443C' : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) ∈
      shortClass := by
  rw [fM_y443C'_op_eq, ← evalGL_slet_eq]
  exact cbar_mul_cbarP_mem_shortClass


theorem hd_primed_fM_of_hd
    (hd : fM y443C * (fM y443X * fM y443C * fM y443X) ≠
      (fM y443X * fM y443C * fM y443X) * fM y443C) :
    fM y443C' * (fM y443X' * fM y443C' * fM y443X') ≠
      (fM y443X' * fM y443C' * fM y443X') * fM y443C' := by
  intro e
  refine hd ?_
  rw [fM_y443C'_conj, fM_y443X'_conj] at e
  have h1 : Grho * (fM y443C * (fM y443X * fM y443C * fM y443X)) * Grho⁻¹ =
      Grho * fM y443C * Grho⁻¹ * (Grho * fM y443X * Grho⁻¹ * (Grho * fM y443C * Grho⁻¹) *
        (Grho * fM y443X * Grho⁻¹)) := by group
  have h2 : Grho * ((fM y443X * fM y443C * fM y443X) * fM y443C) * Grho⁻¹ =
      Grho * fM y443X * Grho⁻¹ * (Grho * fM y443C * Grho⁻¹) * (Grho * fM y443X * Grho⁻¹) *
        (Grho * fM y443C * Grho⁻¹) := by group
  have e2 : Grho * (fM y443C * (fM y443X * fM y443C * fM y443X)) * Grho⁻¹ =
      Grho * ((fM y443X * fM y443C * fM y443X) * fM y443C) * Grho⁻¹ := by
    rw [h1, h2]
    exact e
  exact mul_left_cancel (mul_right_cancel e2)


end CFSG.YGroups.Y443
