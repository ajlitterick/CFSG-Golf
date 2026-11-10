module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aIrred

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

open CFSG.QuasithinUnique.Setup.X7

section Coordinates

variable {F : Type*} [Field F] [CharP F 2] [Fintype F] (k : Type*) [Field k] [Algebra F k]
  [CharP k 2] {f : ℕ}


end Coordinates

section Duality

variable {F : Type*} [Field F] [CharP F 2] [Fintype F] (k : Type*) [Field k] [Algebra F k]
  [CharP k 2] {f : ℕ}

@[expose] def frobPow (F : Type*) [Field F] [CharP F 2] : ℕ → (SL(3, F) →* SL(3, F))
  | 0 => MonoidHom.id _
  | r + 1 => (frobSL F).comp (frobPow F r)

omit [Fintype F] in
theorem frobSL_coe (h : SL(3, F)) :
    ((frobSL F h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (h : Matrix (Fin 3) (Fin 3) F).map (fun x => x ^ 2) := by
  ext i j
  simp [frobSL, Matrix.SpecialLinearGroup.map_apply_coe, frobenius_def]


omit [Fintype F] in
theorem frobSL_iterate_coe (n : ℕ) (g : SL(3, F)) :
    (((frobSL F)^[n] g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F).map (fun x => x ^ 2 ^ n) := by
  induction n generalizing g with
  | zero => ext i j; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', frobSL_coe, ih]
    ext i j
    simp only [Matrix.map_apply]
    rw [← pow_mul, pow_succ]

theorem frobSL_iterate_card (hF : Fintype.card F = 2 ^ f) (g : SL(3, F)) :
    (frobSL F)^[f] g = g := by
  apply Subtype.ext
  rw [frobSL_iterate_coe]
  ext i j
  simp only [Matrix.map_apply]
  rw [← hF, FiniteField.pow_card]

theorem tensorRep_comp_frobPow (hF : Fintype.card F = 2 ^ f) (r : ℕ) :
    ∀ a b : Fin f → Bool,
      ∃ (P : Matrix (TIdx f ((shiftBits f)^[r] a) ((shiftBits f)^[r] b)) (TIdx f a b) k)
        (Q : Matrix (TIdx f a b) (TIdx f ((shiftBits f)^[r] a) ((shiftBits f)^[r] b)) k),
        MatIso ((tensorRep (F := F) k a b).comp (frobPow F r))
          (tensorRep k ((shiftBits f)^[r] a) ((shiftBits f)^[r] b)) P Q := by
  induction r with
  | zero =>
    intro a b
    exact ⟨_, _, MatIso.refl (tensorRep (F := F) k a b)⟩
  | succ r ih =>
    intro a b
    obtain ⟨P₁, Q₁, h₁⟩ := tensorRep_comp_frob k hF a b
    obtain ⟨P₂, Q₂, h₂⟩ := ih (shiftBits f a) (shiftBits f b)
    have h3 := (h₁.comp (frobPow F r)).trans h₂
    exact ⟨_, _, by
      rw [frobPow, ← MonoidHom.comp_assoc]
      exact h3⟩


end Duality

section Orbits


end Orbits

end CFSG.QuasithinUnique.Setup.X7a
