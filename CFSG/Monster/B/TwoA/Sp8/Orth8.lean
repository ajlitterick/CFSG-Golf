
module


public import CFSG.Monster.B.TwoA.Sp8.Orth8Forms
public import CFSG.Monster.B.TwoA.Sp8.Orth8Pairs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA

@[expose] def cOrbit :
    Set Dfull := {y | ∃ x ∈ Xgrp, x * cQ * x⁻¹ = y}

theorem mem_cOrbit_iff
    {y : Dfull} : y ∈ cOrbit ↔ ∃ v : V8, qPoly v = 0 ∧ cQ * Psi v = y := by
  rw [cOrbit, orbit_cQ]
  rfl

theorem cOrbit_two_transitive
    {y₁ y₂ y₃ y₄ : Dfull} (h1 : y₁ ∈ cOrbit) (h2 : y₂ ∈ cOrbit)
    (h3 : y₃ ∈ cOrbit) (h4 : y₄ ∈ cOrbit) (h12 : y₁ ≠ y₂) (h34 : y₃ ≠ y₄) :
    ∃ x ∈ Xgrp, x * y₁ * x⁻¹ = y₃ ∧ x * y₂ * x⁻¹ = y₄ := by
  obtain ⟨v₁, hv₁, rfl⟩ := mem_cOrbit_iff.1 h1
  obtain ⟨v₂, hv₂, rfl⟩ := mem_cOrbit_iff.1 h2
  obtain ⟨v₃, hv₃, rfl⟩ := mem_cOrbit_iff.1 h3
  obtain ⟨v₄, hv₄, rfl⟩ := mem_cOrbit_iff.1 h4
  exact orbit_two_transitive hv₁ hv₂ (fun h => h12 (h ▸ rfl)) hv₃ hv₄ (fun h => h34 (h ▸ rfl))


end CFSG.Monster.B.TwoA.Sp8
