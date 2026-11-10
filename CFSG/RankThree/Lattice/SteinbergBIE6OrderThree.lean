module

public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIPoly

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 RootSpace Polynomial

@[expose] def e6T3Word : List (Fin 6) := [0, 1, 2, 3, 4, 5]

@[expose] def e6T3W : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd (e6Word e6T3Word) ^ 4

@[expose] def e6T3MList : List (List ℤ) :=
  [[0, 0, 0, 0, 0, -1], [1, 0, 0, 0, -1, 0], [1, 1, 0, -1, 0, -1], [1, 1, 1, -1, -1, -1],
    [1, 1, 0, 0, -1, -1], [1, 0, 0, 0, 0, -1]]

@[expose] def e6T3Supports : List (Finset (Fin Tag.E6.rank)) :=
  [∅, {0, 2}, {1, 3}, {2, 3}, {3, 4}, {4, 5}, {0, 2, 4, 5}, {1, 2, 3, 4}]


theorem e6T3W_eq_wordProd : e6T3W = (coxeterSystem Tag.E6).wordProd
    (e6Word e6T3Word ++ e6Word e6T3Word ++ e6Word e6T3Word ++ e6Word e6T3Word) := by
  simp only [e6T3W, pow_succ, pow_zero, one_mul, CoxeterSystem.wordProd_append]

theorem weylMatrix_e6T3W : weylMatrix e6T3W = toMat Tag.E6.rank e6T3MList := by
  rw [e6T3W_eq_wordProd]
  exact weylMatrix_wordProd_e6 (ω := e6T3Word ++ e6T3Word ++ e6T3Word ++ e6T3Word)
    (by decide +kernel)

theorem e6T3_sq : toMat Tag.E6.rank e6T3MList * toMat Tag.E6.rank e6T3MList +
    toMat Tag.E6.rank e6T3MList + 1 = 0 := by
  rw [← toMat_lmul, ← toMat_ladd, ← toMat_lid, ← toMat_ladd, ← toMat_lzero]
  exact congrArg (toMat Tag.E6.rank) (by decide +kernel)

theorem e6T3_cube : e6T3W ^ 3 = 1 := by
  apply weylMatrix_injective
  rw [weylMatrix_pow, weylMatrix_e6T3W, weylMatrix_one, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E6.rank) (by decide +kernel)

theorem weyl_smul_add (g : WeylGroup Tag.E6) (x y : Fin Tag.E6.rank → ℤ) :
    g • (x + y) = g • x + g • y := by
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, ← weylMatrix_mulVec, Matrix.mulVec_add]

theorem weyl_smul_zero (g : WeylGroup Tag.E6) : g • (0 : Fin Tag.E6.rank → ℤ) = 0 := by
  rw [← weylMatrix_mulVec, Matrix.mulVec_zero]

theorem e6T3_lattice (x : Fin Tag.E6.rank → ℤ) : e6T3W • e6T3W • x + e6T3W • x + x = 0 := by
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, weylMatrix_e6T3W,
    Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.one_mulVec x, Matrix.mulVec_mulVec,
    Matrix.mul_one, ← Matrix.add_mulVec, e6T3_sq, Matrix.zero_mulVec]

theorem e6T3_real (y : RootSpace Tag.E6) :
    weylAct Tag.E6 e6T3W (weylAct Tag.E6 e6T3W y) + weylAct Tag.E6 e6T3W y + y = 0 := by
  have key : ∀ i, weylAct Tag.E6 e6T3W (weylAct Tag.E6 e6T3W (ofLattice (Pi.single i 1))) +
      weylAct Tag.E6 e6T3W (ofLattice (Pi.single i 1)) + ofLattice (Pi.single i 1) = 0 := by
    intro i
    rw [weylAct_ofLattice, weylAct_ofLattice, ← ofLattice_add, ← ofLattice_add, e6T3_lattice,
      ofLattice_zero]
  conv_lhs => rw [← sum_smul_ofLattice_single y]
  simp only [map_sum, map_smul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← smul_add, ← smul_add, key, smul_zero]

theorem e6T3_real_fixed {y : RootSpace Tag.E6} (h : weylAct Tag.E6 e6T3W y = y) : y = 0 := by
  have h3 := e6T3_real y
  rw [h, h] at h3
  have : (3 : ℝ) • y = 0 := by rw [← h3]; module
  exact (smul_eq_zero.1 this).resolve_left (by norm_num)

theorem e6T3_lattice_fixed {x : Fin Tag.E6.rank → ℤ} (h : e6T3W • x = x) : x = 0 := by
  have h3 := e6T3_lattice x
  rw [h, h] at h3
  funext i
  have := congrFun h3 i
  simp only [Pi.add_apply, Pi.zero_apply] at this
  rw [Pi.zero_apply]
  omega

theorem weylMatrix_sq_add_of_smul {T : WeylGroup Tag.E6}
    (hT : ∀ x : Fin Tag.E6.rank → ℤ, T • T • x + T • x + x = 0) :
    weylMatrix T * weylMatrix T + weylMatrix T + 1 = 0 := by
  ext i j
  have h := congrFun (hT (Pi.single j 1)) i
  rw [Matrix.add_apply, Matrix.add_apply, ← weylMatrix_mul, weylMatrix_apply, weylMatrix_apply,
    mul_smul, Matrix.one_apply, Matrix.zero_apply]
  simp only [Pi.add_apply, Pi.zero_apply, Pi.single_apply] at h
  exact h

theorem e6T3_supports_complete : ∀ S : Finset (Fin Tag.E6.rank), S ≠ Finset.univ →
    S.card % 2 = 0 →
    (Finset.univ.filter fun m : Fin 72 => ∀ i, i ∉ S → e6RootVec m i = 0).card % 3 = 0 →
    S ∈ e6T3Supports := by
  decide +kernel

theorem e6T3_parabolic_card (S : Finset (Fin Tag.E6.rank)) :
    (parabolicRoots Tag.E6 ↑S).ncard =
      (Finset.univ.filter fun m : Fin 72 => ∀ i, i ∉ S → e6RootVec m i = 0).card :=
  ncard_parabolicRoots_eq (P := fun i => i ∈ S) (fun _ => Finset.mem_coe) rfl

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩


end CFSG.RankThree.Lattice
