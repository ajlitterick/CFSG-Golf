module

public import CFSG.LieType.SpecialLinear.EndNode.Radicals

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LieType.Universal.SpecialLinear

noncomputable section

variable (m : ℕ) (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

@[expose] def endSwap : Equiv.Perm (Fin (m+2)) :=
  Equiv.swap 0 (Fin.last (m+1))

@[expose] def endSigns : Fin (m+2) → F :=
  fun i => if i = 0 then -1 else 1


omit [Finite F] in
private theorem prod_endSigns : (∏ i : Fin (m+2), endSigns m F i) = -1 := by
  rw [Fintype.prod_eq_single (0 : Fin (m+2))]
  · simp [endSigns]
  · intro b hb
    simp [endSigns, hb]

omit [Finite F] in
private theorem signedPerm_endSigns_eq_permMatrix_mul_diagonal :
    signedPerm (endSwap m) (endSigns m F) =
      ((endSwap m)⁻¹).permMatrix F * diagonal (endSigns m F) := by
  ext a b
  rw [Matrix.mul_diagonal, signedPerm_apply]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, Equiv.Perm.inv_eq_iff_eq]
  split_ifs <;> simp

omit [Finite F] in
theorem det_endSigns : (signedPerm (endSwap m) (endSigns m F)).det = 1 := by
  rw [signedPerm_endSigns_eq_permMatrix_mul_diagonal, Matrix.det_mul,
    Matrix.det_permutation, Matrix.det_diagonal, Equiv.Perm.sign_inv]
  unfold endSwap
  rw [Equiv.Perm.sign_swap (by simp)]
  rw [prod_endSigns]
  norm_num

@[expose] def endMonomial : SLm2 m F :=
  ⟨signedPerm (endSwap m) (endSigns m F), det_endSigns m F⟩

omit [Finite F] in
@[simp] theorem coe_endMonomial :
    (endMonomial m F : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      signedPerm (endSwap m) (endSigns m F) := rfl


end

end CFSG.LieType.SpecialLinear
