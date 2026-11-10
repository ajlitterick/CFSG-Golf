
module

public import CFSG.Sporadic.Schreier.J4SFormBase

public import CFSG.Sporadic.Schreier.J4SCheck

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem jq_vecMul
    (g : J) (v : Fin 112 → ZMod 2) : jq (v ᵥ* φ g) = jq v := by
  have hg : g ∈ Subgroup.closure ({a, b} : Set J) := by rw [closure_ab]; exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction generalizing v with
  | mem g hg =>
    rcases hg with rfl | rfl
    · rw [← (rep_a matFacts).2.2.1]
      exact jq_vecMul_seed (defectOK_spec formDefect_check.1) v
    · rw [← (rep_b matFacts).2.2.1]
      exact jq_vecMul_seed (defectOK_spec formDefect_check.2) v
  | one => rw [map_one, Matrix.vecMul_one]
  | mul g h _ _ ihg ihh => rw [map_mul, ← Matrix.vecMul_vecMul, ihh, ihg]
  | inv g _ ih =>
    have e : v = (v ᵥ* φ g⁻¹) ᵥ* φ g := by
      rw [Matrix.vecMul_vecMul, ← map_mul, inv_mul_cancel, map_one, Matrix.vecMul_one]
    conv_rhs => rw [e]
    rw [ih]


end CFSG.Sporadic.J4Schreier
