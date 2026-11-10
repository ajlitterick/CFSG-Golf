module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Alg
public import CFSG.Quasithin.H13.A6Nu
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.A6

open Matrix Subgroup CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def cols4 (a b c d : Fin 4 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun i j => ![a, b, c, d] j i

theorem cols4_mulVec (a b c d x : Fin 4 → ZMod 2) :
    (cols4 a b c d).mulVec x = x 0 • a + x 1 • b + x 2 • c + x 3 • d := by
  funext i
  simp [cols4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

theorem zmodTwo_cases : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by
  decide

theorem add_self_vec4 (x : Fin 4 → ZMod 2) : x + x = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  rcases zmodTwo_cases (x i) with h | h <;> rw [h] <;> decide

theorem eq_of_add_eq_zero_vec4 {x y : Fin 4 → ZMod 2} (h : x + y = 0) : x = y := by
  have e : x = x + y + y := by rw [add_assoc, add_self_vec4, add_zero]
  rw [e, h, zero_add]

theorem pair_indep4 {v w : Fin 4 → ZMod 2} (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w) {s t : ZMod 2}
    (h : s • v + t • w = 0) : s = 0 ∧ t = 0 := by
  rcases zmodTwo_cases s with rfl | rfl <;> rcases zmodTwo_cases t with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · simp only [zero_smul, one_smul, zero_add] at h
    exact absurd h hw
  · simp only [zero_smul, one_smul, add_zero] at h
    exact absurd h hv
  · simp only [one_smul] at h
    exact absurd (eq_of_add_eq_zero_vec4 h) hvw

theorem isUnit_cols4 {a b c d : Fin 4 → ZMod 2}
    (h : ∀ x : Fin 4 → ZMod 2, x 0 • a + x 1 • b + x 2 • c + x 3 • d = 0 → x = 0) :
    IsUnit (cols4 a b c d) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have h0 : (cols4 a b c d).mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  rw [cols4_mulVec] at h0
  exact sub_eq_zero.mp (h _ h0)

theorem card_vec4 : Fintype.card (Fin 4 → ZMod 2) = 16 := by
  simp [ZMod.card]

section Chief


end Chief

end CFSG.Quasithin.H13.A6
