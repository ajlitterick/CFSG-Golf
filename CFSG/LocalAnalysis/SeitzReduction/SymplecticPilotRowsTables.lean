module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRows
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTables

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG.SeitzReduction.F4Pilot (ordSL ordSU ordSL_two ordSL_three ordSU_three)


private theorem cast_add_two_pow_sub_one' (p j : ℕ) :
    (((p + 2) ^ j - 1 : ℕ) : ℤ) = ((p : ℤ) + 2) ^ j - 1 := by
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
  push_cast
  ring

theorem ordSL_two_sq_lt_ordSL_two_sq {q : ℕ} (hq : 2 ≤ q) : ordSL 2 q ^ 2 < ordSL 2 (q ^ 2) := by
  rw [ordSL_two, ordSL_two, ← pow_mul]
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
  zify
  simp only [cast_add_two_pow_sub_one']
  rw [← sub_pos]
  ring_nf
  positivity


end CFSG.SeitzReduction.SymplecticPilot
