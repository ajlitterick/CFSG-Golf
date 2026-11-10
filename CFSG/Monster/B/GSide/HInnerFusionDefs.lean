module

public import CFSG.Monster.B.GSide.HInnerFusion

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open MulOpposite CFSG.Monster.B CFSG.Monster.B.CTIB CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Amalgam

theorem xs_mul_labelS : xs * labelS = labelS * xs := by
  have h := conj_xs (g := labelS) (Ebar_le_Jbar labelS_mem)
  calc xs * labelS = labelS * (labelS⁻¹ * xs * labelS) := by group
    _ = labelS * xs := by rw [h]

theorem xhatS_mem_vStab :
    xhatS ∈ vStab cv0 := by
  rw [← sEquiv_xs]
  exact (commute_labelS_iff_mem xs).1 xs_mul_labelS

@[expose] def xhatH :
    vStab cv0 := ⟨xhatS, xhatS_mem_vStab⟩

theorem coe_xhatH :
    (xhatH : Shat) = xhatS := rfl

theorem sEquiv_symm_xhatH :
    sEquiv.symm (xhatH : Shat) = xs := by
  rw [coe_xhatH, ← sEquiv_xs, MulEquiv.symm_apply_apply]

@[expose] def OuterTwoC :
    Prop :=
  ∀ y : vStab cv0, y * xhatH = xhatH * y → y * y = 1 →
    (rkH y = 2158 ∨ rkH (cV0 * y) = 2158) → y ∉ commutator (vStab cv0)

end CFSG.Monster.B.GSide
