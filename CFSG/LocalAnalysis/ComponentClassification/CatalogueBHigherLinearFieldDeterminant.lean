module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldFixed

public section

namespace CFSG.ComponentClassification.CatalogueBHigherLinearField

noncomputable section

open Matrix CatalogueBHigherLinearAction

universe u

theorem mk_mem_pslRange_iff_det_power (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) :
    ProjGenLinGroup.mk A ∈ pslRange n K ↔
      ∃ c : Kˣ, c ^ n = GeneralLinearGroup.det A := by
  rw [pslRange_eq_map]
  constructor
  · rintro ⟨B, hB, hBA⟩
    obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hBA
    have hdetB : GeneralLinearGroup.det B = 1 := by
      rw [CatalogueBGeneralLinear.specialLinearRange_eq_detKernel] at hB
      exact hB
    refine ⟨c, ?_⟩
    have hdet := congrArg GeneralLinearGroup.det hc
    simpa only [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin,
      hdetB, one_mul] using hdet
  · rintro ⟨c, hc⟩
    let B : GL (Fin n) K := A * GeneralLinearGroup.scalar (Fin n) c⁻¹
    have hdetB : GeneralLinearGroup.det B = 1 := by
      change GeneralLinearGroup.det (A * GeneralLinearGroup.scalar (Fin n) c⁻¹) = 1
      rw [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, ← hc, inv_pow,
        mul_inv_cancel]
    refine ⟨B, ?_, ?_⟩
    · rw [CatalogueBGeneralLinear.specialLinearRange_eq_detKernel]
      exact hdetB
    · change ProjGenLinGroup.mk (A * GeneralLinearGroup.scalar (Fin n) c⁻¹) = _
      rw [map_mul, ProjGenLinGroup.mk_scalar, mul_one]

theorem subfield_projectivity_mem_pslRange_iff (n : ℕ) (K : Type u) [Field K]
    (S : Subfield K) (B : GL (Fin n) S) :
    subfieldPGLMap (Fin n) K S (ProjGenLinGroup.mk B) ∈ pslRange n K ↔
      ∃ c : Kˣ, c ^ n = Units.map S.subtype (GeneralLinearGroup.det B) := by
  rw [subfieldPGLMap_mk, mk_mem_pslRange_iff_det_power]
  rw [GeneralLinearGroup.map_det]


end

end CFSG.ComponentClassification.CatalogueBHigherLinearField
