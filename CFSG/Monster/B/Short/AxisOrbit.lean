module

public import CFSG.Monster.Generated.Centralizer
public import CFSG.Monster.Griess.AutFinite

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Short

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated

@[expose] def rStar : Q := SpinLattice.DQ (deltaPair 0 1)

@[expose] def aStar : SpaceB := axis rStar

@[expose] def tStar : SpaceB ≃ₗ[ℚ] SpaceB := rhoEquiv rStar

@[expose] def axisOrbit : Set SpaceB := {a | ∃ g ∈ Gmat, g aStar = a}

@[expose] def shortClass : Set (SpaceB ≃ₗ[ℚ] SpaceB) := {t | ∃ g ∈ Gmat, g * tStar * g⁻¹ = t}

@[expose] def tAxis (a : SpaceB) : Module.End ℚ SpaceB :=
  1 - (16 / 217 : ℚ) • (gmul a * (gmul a - (4 : ℚ) • 1) * (gmul a - (16 : ℚ) • 1))

theorem rStar_eq_rMinus : rStar = rMinus 0 1 := rfl

theorem coordOf_rStar : coordOf rStar = (0, deltaPair 0 1) := coordOf_rMinus 0 1

theorem isShortCoord_rStar : IsShortCoord (coordOf rStar) :=
  isShortCoord_rMinus (by decide : (0 : Fin 24) < 1)

theorem vMinus_zero_one_mem : vMinus 0 1 ∈ minVecs := vMinus_mem (by decide : (0 : Fin 24) < 1)

theorem phi0_coordOf_rStar : phi0 (coordOf rStar) = classOf (vMinus 0 1) :=
  phi0_coordOf_rMinus (by decide : (0 : Fin 24) < 1)

theorem vMinus_zero_one : vMinus 0 1 = (4 : ℤ) • eℤ 0 - (4 : ℤ) • eℤ 1 := rfl

theorem coe_axisE_rStar : (axisE rStar : Matrix (Fin 24) (Fin 24) ℚ) = projMat (vMinus 0 1) :=
  coe_axisE_rMinus (by decide : (0 : Fin 24) < 1)

theorem aStar_eq : aStar =
    (2 : ℚ) • ((axisE rStar, 0, 0) : SpaceB) - (2 : ℚ) • ((0, Xlift rStar, 0) : SpaceB) := rfl

theorem tStar_mem_Gvis : tStar ∈ Gvis := rhoEquiv_mem_Gvis rStar

theorem tStar_mem_Gmat : tStar ∈ Gmat := Hmat_le_Gmat tStar_mem_Gvis

theorem aStar_mem_axisOrbit : aStar ∈ axisOrbit := ⟨1, one_mem _, rfl⟩


theorem tAxis_apply (a v : SpaceB) :
    tAxis a v = v - (16 / 217 : ℚ) •
      gmul a (gmul a (gmul a v) - (4 : ℚ) • gmul a v - (16 : ℚ) • (gmul a v - (4 : ℚ) • v)) := by
  simp only [tAxis, LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply,
    Module.End.mul_apply, map_sub, map_smul]


end CFSG.Monster.B.Short
