module

public import CFSG.Quasithin.AppendixH.H16.OctadMask
public import CFSG.Quasithin.AppendixH.Common.OctadPtStabCard

public section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH


theorem octStab_octad0_le_AutPerm : octStab octad0 ≤ AutPerm := inf_le_left


theorem imgCd_fixO_normal :
    ∀ g ∈ imgCd (octStab octad0), ∀ k ∈ imgCd fixO, g * k * g⁻¹ ∈ imgCd fixO := by
  have hN : octStab octad0 ≤ Subgroup.normalizer (fixO : Set (Equiv.Perm (Fin 24))) := by
    rw [← octFix_octad0]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (octFix_le_octStab octad0)).1
      (normal_octFix octad0)
  intro g hg k hk
  have hmem := imgCd_le_normalizer (Γ := octStab octad0) (Δ := fixO) hN hg
  exact (Subgroup.mem_normalizer_iff.1 hmem k).1 hk

theorem isActsInv_octV1 : IsActsInv (actsOnModule (imgCd (octStab octad0))) octV1 := by
  rintro f ⟨y, hy, rfl⟩ v hv
  rw [← fixV_imgCd_fixO] at hv ⊢
  intro k hk
  have h1 : y⁻¹ ∈ imgCd (octStab octad0) := Subgroup.inv_mem _ hy
  have hmem : y⁻¹ * k * y ∈ imgCd fixO := by
    have h := imgCd_fixO_normal y⁻¹ h1 k hk
    simpa using h
  have hconj : y⁻¹ (k (y v)) = v := by
    have h := (mem_fixV.1 hv) (y⁻¹ * k * y) hmem
    simpa using h
  change k (y v) = y v
  calc k (y v) = y (y⁻¹ (k (y v))) := (MulEquiv.apply_symm_apply y _).symm
    _ = y v := by rw [hconj]


end CFSG.ASVolI.H16
