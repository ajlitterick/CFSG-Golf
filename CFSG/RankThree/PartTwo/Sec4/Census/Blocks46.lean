module

public import CFSG.RankThree.PartTwo.Census.Classical.EvenBlocks
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
import CFSG.LocalAnalysis.SectionRank.QTK.EvenBlocks3

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open Matrix CFSG.Assembly CFSG.Assembly.RankThreeEven
open CFSG.RankThree.PartTwo.Census (threeCycleMat threeCycleMat_pow_three threeCycleMat_pow_val_add
  threeCycleMat_pow_val_zero_one det_threeCycleMat eq_one_of_mul_self_eq_one isElemAbelian_range
  le_localRank_quotient_of_le_normalizer le_normalizer_of_conj_mem pslReindex
  localRank_eq_of_mulEquiv)

variable {K : Type} [Field K] [CharP K 2]

@[expose] def sBlockMat3 (a : Fin 3 → ZMod 3) : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K :=
  blockDiagonal fun b => threeCycleMat K ^ (a b).val

theorem sBlockMat3_add (a a' : Fin 3 → ZMod 3) :
    sBlockMat3 (K := K) (a + a') = sBlockMat3 a * sBlockMat3 a' := by
  rw [sBlockMat3, sBlockMat3, sBlockMat3, ← blockDiagonal_mul]
  congr 1
  funext b
  rw [Pi.add_apply, threeCycleMat_pow_val_add]

theorem det_sBlockMat3 (a : Fin 3 → ZMod 3) : (sBlockMat3 (K := K) a).det = 1 := by
  rw [sBlockMat3, det_blockDiagonal]
  exact Finset.prod_eq_one fun b _ => by rw [det_pow, det_threeCycleMat, one_pow]

abbrev BlockIdx3 (m : ℕ) : Type := (Fin 2 × Fin 3) ⊕ Fin m

@[expose] def sHom3 (m : ℕ) (K : Type) [Field K] [CharP K 2] :
    Multiplicative (Fin 3 → ZMod 3) →* SpecialLinearGroup (BlockIdx3 m) K where
  toFun a := ⟨fromBlocks (sBlockMat3 a.toAdd) 0 0 1, by
    rw [det_fromBlocks_zero₂₁, det_sBlockMat3, det_one, mul_one]⟩
  map_one' := Subtype.ext (by
    change fromBlocks (sBlockMat3 (0 : Fin 3 → ZMod 3)) 0 0 1 = (1 : Matrix (BlockIdx3 m) _ K)
    rw [← fromBlocks_one, sBlockMat3]
    congr 1
    rw [← blockDiagonal_one]
    congr 1)
  map_mul' a b := Subtype.ext (by
    change fromBlocks (sBlockMat3 (a.toAdd + b.toAdd)) 0 0 1 =
      fromBlocks (sBlockMat3 (K := K) a.toAdd) 0 0 1 * fromBlocks (sBlockMat3 b.toAdd) 0 0 1
    rw [fromBlocks_multiply, sBlockMat3_add]
    simp)


@[expose] def yMat3 (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K :=
  Matrix.of fun ib jb => if ib.2 = 0 ∧ jb.2 = 1 then X ib.1 jb.1 else 0

omit [CharP K 2] in
theorem yMat3_mul_yMat3 (X X' : Matrix (Fin 2) (Fin 2) K) : yMat3 X * yMat3 X' = 0 := by
  ext ib jb
  simp only [mul_apply, yMat3, of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun kc _ => ?_
  by_cases h : kc.2 = 1
  · have : ¬ (kc.2 = 0 ∧ jb.2 = 1) := fun h' => by rw [h] at h'; exact absurd h'.1 (by decide)
    rw [ite_eq_right this, mul_zero]
  · have : ¬ (ib.2 = 0 ∧ kc.2 = 1) := fun h' => h h'.2
    rw [ite_eq_right this, zero_mul]

omit [CharP K 2] in
theorem yMat3_zero : yMat3 (0 : Matrix (Fin 2) (Fin 2) K) = 0 := by
  ext ib jb
  simp [yMat3]

omit [CharP K 2] in
theorem yMat3_add (X X' : Matrix (Fin 2) (Fin 2) K) : yMat3 (X + X') = yMat3 X + yMat3 X' := by
  ext ib jb
  simp only [yMat3, of_apply, Matrix.add_apply]
  split_ifs <;> simp

omit [CharP K 2] in
theorem one_add_yMat3_mul (X X' : Matrix (Fin 2) (Fin 2) K) :
    (1 + yMat3 X) * (1 + yMat3 X') = 1 + yMat3 (X + X') := by
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, yMat3_mul_yMat3, add_zero, yMat3_add]
  abel

theorem det_one_add_yMat3 (X : Matrix (Fin 2) (Fin 2) K) : (1 + yMat3 X).det = 1 := by
  have hX : X + X = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply, CharTwo.add_self_eq_zero]
  refine eq_one_of_mul_self_eq_one ?_
  rw [← det_mul, one_add_yMat3_mul, hX, yMat3_zero, add_zero, det_one]

@[expose] def uHom3 (m : ℕ) (K : Type) [Field K] [CharP K 2] :
    Multiplicative (Matrix (Fin 2) (Fin 2) K) →* SpecialLinearGroup (BlockIdx3 m) K where
  toFun X := ⟨fromBlocks (1 + yMat3 X.toAdd) 0 0 1, by
    rw [det_fromBlocks_zero₂₁, det_one_add_yMat3, det_one, mul_one]⟩
  map_one' := Subtype.ext (by
    change fromBlocks (1 + yMat3 (0 : Matrix (Fin 2) (Fin 2) K)) 0 0 1 =
      (1 : Matrix (BlockIdx3 m) _ K)
    rw [← fromBlocks_one, yMat3_zero, add_zero])
  map_mul' X X' := Subtype.ext (by
    change fromBlocks (1 + yMat3 (X.toAdd + X'.toAdd)) 0 0 1 =
      fromBlocks (1 + yMat3 (K := K) X.toAdd) 0 0 1 * fromBlocks (1 + yMat3 X'.toAdd) 0 0 1
    rw [fromBlocks_multiply, one_add_yMat3_mul]
    simp)


theorem three_le_localRank_PSL_of_six_le [Finite K] {n : ℕ} (hn : 6 ≤ n) :
    3 ≤ localRank 3 (ProjectiveSpecialLinearGroup (Fin n) K) :=
  CFSG.SectionRank.QTK.three_le_localRank_PSL_of_six_le hn

theorem three_le_localRank_projSL_two {n : ℕ} (hn : 6 ≤ n) [Finite (projSL n (GaloisField 2 1))] :
    3 ≤ localRank 3 (projSL n (GaloisField 2 1)) := by
  rw [← localRank_eq_of_mulEquiv (pslEquivProjSL n (GaloisField 2 1)) Nat.prime_three]
  exact three_le_localRank_PSL_of_six_le hn

end CFSG.RankThree.PartTwo.Sec4.Census
