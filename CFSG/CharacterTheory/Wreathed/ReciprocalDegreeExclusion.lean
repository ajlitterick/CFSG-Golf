module

public import CFSG.CharacterTheory.Wreathed.TwoPartArithmetic
public import CFSG.CharacterTheory.Wreathed.CharacterDegreeCongruence

public noncomputable section

namespace CFSG.Wreathed

@[expose] def modFourSign (q : ℕ) : ℤ := if q % 4 = 1 then 1 else -1

theorem modFourSign_cases (q : ℕ) : modFourSign q = 1 ∨ modFourSign q = -1 := by
  unfold modFourSign
  split <;> simp


end CFSG.Wreathed
