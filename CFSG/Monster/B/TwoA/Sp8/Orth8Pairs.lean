
module

public import CFSG.Monster.B.TwoA.Sp8.Orth8PairsBase

public import CFSG.Monster.B.TwoA.Sp8.Orth8Image

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA

theorem orbit_two_transitive
    {v₁ v₂ w₁ w₂ : V8} (h1 : qPoly v₁ = 0) (h2 : qPoly v₂ = 0)
    (h12 : v₁ ≠ v₂) (h3 : qPoly w₁ = 0) (h4 : qPoly w₂ = 0) (h34 : w₁ ≠ w₂) :
    ∃ x ∈ Xgrp, x * (cQ * Psi v₁) * x⁻¹ = cQ * Psi w₁ ∧
      x * (cQ * Psi v₂) * x⁻¹ = cQ * Psi w₂ := by
  obtain ⟨x, hx, hx1, hx2⟩ := reach_of_vec h1 h2 h12
  obtain ⟨y, hy, hy1, hy2⟩ := reach_of_vec h3 h4 h34
  refine ⟨y * x⁻¹, Xgrp.mul_mem hy (Xgrp.inv_mem hx), ?_, ?_⟩
  · have e : cQ * Psi v₁ = x * cQ * x⁻¹ := hx1.symm
    rw [e, show y * x⁻¹ * (x * cQ * x⁻¹) * (y * x⁻¹)⁻¹ = y * cQ * y⁻¹ by group, hy1]
  · have e : cQ * Psi v₂ = x * (cQ * xhat) * x⁻¹ := hx2.symm
    rw [e, show y * x⁻¹ * (x * (cQ * xhat) * x⁻¹) * (y * x⁻¹)⁻¹ = y * (cQ * xhat) * y⁻¹ by group,
      hy2]


end CFSG.Monster.B.TwoA.Sp8
