module

public import CFSG.LocalAnalysis.RankThreeUC.Section9.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section9.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.Y2ConjugationInvariance

open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.Section9 CFSG.Open CFSG.LocalAnalysis.RankThreeUC SourceSetting Subgroup

variable {G : Type} [Group G] [Finite G]

theorem map_conj_eq_self {M : Subgroup G} {g : G} (hg : g ∈ M) :
    M.map (MulAut.conj g).toMonoidHom = M := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact M.mul_mem (M.mul_mem hg hy) (M.inv_mem hg)
  · intro hx
    exact ⟨g⁻¹ * x * g, M.mul_mem (M.mul_mem (M.inv_mem hg) hx) hg, by simp [mul_assoc]⟩

theorem map_le_map_iff (g : G) {X Z : Subgroup G} :
    X.map (MulAut.conj g).toMonoidHom ≤ Z.map (MulAut.conj g).toMonoidHom ↔ X ≤ Z :=
  Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective

theorem map_inj (g : G) {X Z : Subgroup G} :
    X.map (MulAut.conj g).toMonoidHom = Z.map (MulAut.conj g).toMonoidHom ↔ X = Z :=
  (Subgroup.map_injective (MulAut.conj g).injective).eq_iff


theorem map_oPrimeResidual (g : G) (p : ℕ) (Y : Subgroup G) :
    (oPrimeResidual p Y).map (MulAut.conj g).toMonoidHom =
      oPrimeResidual p (Y.map (MulAut.conj g).toMonoidHom) := by
  unfold oPrimeResidual
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Subgroup.mem_map]
  constructor
  · rintro ⟨y, ⟨hy, k, hk⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, k, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]; exact hk⟩
  · rintro ⟨⟨y, hy, rfl⟩, k, hk⟩
    exact ⟨y, ⟨hy, k, by rw [← hk, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]⟩, rfl⟩

theorem map_map_conj (a b : G) (X : Subgroup G) :
    (X.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      X.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]


theorem map_le_map_conj_mul_iff (g h : G) (A B : Subgroup G) :
    A.map (MulAut.conj g).toMonoidHom ≤ B.map (MulAut.conj (g * h)).toMonoidHom ↔
      A ≤ B.map (MulAut.conj h).toMonoidHom := by
  rw [← map_map_conj, map_le_map_iff]

theorem mem_uniqueSet_map_iff {M : Subgroup G} {g : G} (hg : g ∈ M) (D : Subgroup G) :
    D.map (MulAut.conj g).toMonoidHom ∈ uniqueSet M ↔ D ∈ uniqueSet M := by
  have hM := map_conj_eq_self hg
  unfold uniqueSet
  simp only [Set.mem_setOf_eq]
  refine and_congr ?_ ⟨fun H h hh => ?_, fun H h hh => ?_⟩
  · conv_lhs => rw [← hM]
    exact map_le_map_iff g
  · have h1 := H (g * h) ((map_le_map_conj_mul_iff g h D M).mpr hh)
    have h2 := map_map_conj h g M
    rw [h1] at h2
    exact (map_inj g).mp (h2.trans hM.symm)
  · have hh' : D ≤ M.map (MulAut.conj (g⁻¹ * h)).toMonoidHom := by
      rw [← map_le_map_conj_mul_iff g (g⁻¹ * h), mul_inv_cancel_left]; exact hh
    have h1 := H (g⁻¹ * h) hh'
    have h2 := map_map_conj (g⁻¹ * h) g M
    rw [mul_inv_cancel_left, h1, hM] at h2
    exact h2.symm


end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.Y2ConjugationInvariance
