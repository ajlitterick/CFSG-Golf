module

public import CFSG.HardMathSupport.Foote.E27.LieTwo.SpData
public import CFSG.HardMathSupport.Foote.E27.LieTwo.SpModel

public section

namespace CFSG.HardMathSupport.Foote.E27

open Matrix CFSG.Sporadic.He.Native TauCeti


theorem JFin_finSum (r : ℕ) (x y : Fin r ⊕ Fin r) :
    JFin r (ZMod 2) (finSumFinEquiv x) (finSumFinEquiv y) = Matrix.J (Fin r) (ZMod 2) x y := by
  have := congrFun (congrFun (JFin_submatrix r (R := ZMod 2)) x) y
  simpa using this

theorem JFin_zmod_two_apply (r : ℕ) (i j : Fin (r + r)) :
    JFin r (ZMod 2) i j = if i.val + r = j.val ∨ j.val + r = i.val then 1 else 0 := by
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  rw [JFin_finSum]
  rcases x with a | a <;> rcases y with b | b <;>
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.J,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply, Matrix.neg_apply,
      Fin.coe_castAdd, Fin.coe_natAdd]
  · have hc : ¬ (a.val + r = b.val ∨ b.val + r = a.val) := by
      have := a.isLt
      have := b.isLt
      omega
    simp [hc]
  · by_cases hab : a = b
    · subst hab
      have hc : (a.val + r = r + a.val ∨ r + a.val + r = a.val) := Or.inl (Nat.add_comm _ _)
      simp [hc]
    · have h1 : ¬ (a.val + r = r + b.val ∨ r + b.val + r = a.val) := by
        have : a.val ≠ b.val := fun e => hab (Fin.ext e)
        have := a.isLt
        omega
      simp [hab, h1]
  · by_cases hab : a = b
    · subst hab
      have hc : (r + a.val + r = a.val ∨ a.val + r = r + a.val) := Or.inr (Nat.add_comm _ _)
      simp [hc]
    · have h1 : ¬ (r + a.val + r = b.val ∨ b.val + r = r + a.val) := by
        have : a.val ≠ b.val := fun e => hab (Fin.ext e)
        have := b.isLt
        omega
      simp [hab, h1]
  · have hc : ¬ (r + a.val + r = r + b.val ∨ r + b.val + r = r + a.val) := by
      have := a.isLt
      have := b.isLt
      omega
    simp [hc]


end CFSG.HardMathSupport.Foote.E27
