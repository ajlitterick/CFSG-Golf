module

public import CFSG.Milestones.ASVolI.A3Aut.C5Base
public import CFSG.Milestones.ASVolI.A3Aut.SBL3
public import CFSG.Milestones.ASVolI.A2OddAut
public import CFSG.Milestones.ASVolI.A3Aut.Fam
public import CFSG.Milestones.ASVolI.A3Aut.Util

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial

section C5L3

variable {K : Type} [Field K]

theorem burnsideAut_c5L3_fieldAut_mem_U {m : ℕ} (σ : K ≃+* K) {u : LinearFlag.projectiveSL m K}
    (hu : u ∈ LinearFlag.projUnitriangular m K) :
    LinearFlag.fieldAut m K σ u ∈ LinearFlag.projUnitriangular m K := by
  obtain ⟨U, hU, rfl⟩ := hu
  rw [LinearFlag.fieldAut_proj]
  refine ⟨_, ?_, rfl⟩
  obtain ⟨hlow, hdiag⟩ := LinearFlag.mem_unitriangular.1 hU
  refine LinearFlag.mem_unitriangular.2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      hlow i j hij, map_zero]
  · rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      hdiag i, map_one]

theorem burnsideAut_c5L3_map_fieldAut_U {m : ℕ} (σ : K ≃+* K) :
    (LinearFlag.projUnitriangular m K).map (LinearFlag.fieldAut m K σ).toMonoidHom =
      LinearFlag.projUnitriangular m K := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact burnsideAut_c5L3_fieldAut_mem_U σ hy
  · refine ⟨LinearFlag.fieldAut m K σ⁻¹ x, burnsideAut_c5L3_fieldAut_mem_U σ⁻¹ hx, ?_⟩
    change (LinearFlag.fieldAut m K σ * LinearFlag.fieldAut m K σ⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]


end C5L3

end CFSG.ASVolI
