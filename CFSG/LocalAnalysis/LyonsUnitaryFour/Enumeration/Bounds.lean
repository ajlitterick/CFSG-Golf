module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.Rows
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LyonsUnitaryFour

open Matrix

namespace LyonsRow

theorem four_mul_sq_le_strictContribution (r : LyonsRow) (i : Fin 6) :
    4 * r.toVec i ^ 2 ≤ r.strictContribution := by
  obtain ⟨t, a, b, c, d, e⟩ := r
  simp only [strictContribution]
  fin_cases i <;> simp only [toVec] <;> simp
  · nlinarith [sq_nonneg (a + b + c + d + e), sq_nonneg (a - b), sq_nonneg (a - c),
      sq_nonneg (a - d), sq_nonneg (a - e), sq_nonneg (b - c), sq_nonneg (b - d),
      sq_nonneg (b - e), sq_nonneg (c - d), sq_nonneg (c - e), sq_nonneg (d - e)]
  · nlinarith [sq_nonneg t, sq_nonneg (3 * a - (b + c + d + e)), sq_nonneg (b - c),
      sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d), sq_nonneg (c - e),
      sq_nonneg (d - e)]
  · nlinarith [sq_nonneg t, sq_nonneg (3 * b - (a + c + d + e)), sq_nonneg (a - c),
      sq_nonneg (a - d), sq_nonneg (a - e), sq_nonneg (c - d), sq_nonneg (c - e),
      sq_nonneg (d - e)]
  · nlinarith [sq_nonneg t, sq_nonneg (3 * c - (a + b + d + e)), sq_nonneg (a - b),
      sq_nonneg (a - d), sq_nonneg (a - e), sq_nonneg (b - d), sq_nonneg (b - e),
      sq_nonneg (d - e)]
  · nlinarith [sq_nonneg t, sq_nonneg (3 * d - (a + b + c + e)), sq_nonneg (a - b),
      sq_nonneg (a - c), sq_nonneg (a - e), sq_nonneg (b - c), sq_nonneg (b - e),
      sq_nonneg (c - e)]
  · nlinarith [sq_nonneg t, sq_nonneg (3 * e - (a + b + c + d)), sq_nonneg (a - b),
      sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d),
      sq_nonneg (c - d)]

theorem abs_toVec_le_three {r : LyonsRow} (hr : r.strictContribution < 64) (i : Fin 6) :
    |r.toVec i| ≤ 3 := by
  have h := r.four_mul_sq_le_strictContribution i
  rw [abs_le]
  constructor <;> nlinarith


end LyonsRow


@[expose] def lyonsCoordRange : List ℤ := [-3, -2, -1, 0, 1, 2, 3]

theorem mem_lyonsCoordRange {x : ℤ} (h : |x| ≤ 3) : x ∈ lyonsCoordRange := by
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  have : x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide


theorem sum_map_toVec_sq (M : Multiset LyonsRow) (k : Fin 6) :
    (M.map fun r => r.toVec k ^ 2).sum = gramSum M k k := by
  simp only [gramSum_apply, sq]

theorem sum_map_toVec_sub_sq (M : Multiset LyonsRow) (k l : Fin 6) :
    (M.map fun r => (r.toVec k - r.toVec l) ^ 2).sum =
      gramSum M k k + gramSum M l l - 2 * gramSum M k l := by
  simp only [gramSum_apply, ← Multiset.sum_map_mul_left, ← Multiset.sum_map_add,
    ← Multiset.sum_map_sub]
  congr 1
  apply Multiset.map_congr rfl
  intro r _
  ring


end CFSG.LyonsUnitaryFour
