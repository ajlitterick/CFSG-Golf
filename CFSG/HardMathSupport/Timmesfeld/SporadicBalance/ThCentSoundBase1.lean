
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSoundBase

public import CFSG.Sporadic.Th.SimpleBase1

@[expose] public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open scoped Matrix Pointwise


abbrev matJ (g : J) : Matrix (Fin 248) (Fin 248) (ZMod 2) :=
  ((g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem matJ_mul (g h : J) : matJ (g * h) = matJ g * matJ h := by
  simp only [matJ, Subgroup.coe_mul, Units.val_mul]

theorem matJ_one : matJ 1 = 1 := by
  simp only [matJ, OneMemClass.coe_one, Units.val_one]

theorem matJ_pow (g : J) (e : ℕ) : matJ (g ^ e) = matJ g ^ e := by
  induction e with
  | zero => rw [pow_zero, pow_zero, matJ_one]
  | succ e ih => rw [pow_succ, pow_succ, matJ_mul, ih]

theorem rowsMatrix_foldl_mulRows (f : ℤ → Array V4) (gens : ℤ → J)
    (hf : ∀ l, rowsMatrix (f l) = matJ (gens l)) :
    ∀ (w : List ℤ) (acc : Array V4), rowsMatrix (w.foldl (fun acc l => mulRows acc (f l)) acc) =
      rowsMatrix acc * matJ (wordG gens w) := by
  intro w
  induction w with
  | nil => intro acc; simp [wordG, matJ_one]
  | cons l w ih =>
    intro acc
    rw [List.foldl_cons, ih, rowsMatrix_mulRows, hf, wordG_cons, matJ_mul, mul_assoc]

theorem rowsMatrix_wordRows {P Q : Array V4} {g h : J} (hP : rowsMatrix P = matJ g)
    (hQ : rowsMatrix Q = matJ h) (hg : g ^ 2 = 1) (hh : h ^ 3 = 1) (w : List ℤ) :
    rowsMatrix (wordRows P Q w) = matJ (wordG (pairLetters g h) w) := by
  have hg' : g⁻¹ = g := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hg]
  have hh' : h⁻¹ = h * h := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ← pow_succ', hh]
  have hL : ∀ l : ℤ, rowsMatrix (if l = 1 ∨ l = -1 then P else if l = 2 then Q else
      mulRows Q Q) = matJ (pairLetters g h l) := by
    intro l
    unfold pairLetters
    by_cases h1 : l = 1
    · simp only [h1, true_or, ite_true, hP]
    · by_cases h2 : l = -1
      · simp only [h2, or_true, ite_true, show (-1 : ℤ) ≠ 1 by decide, ite_false, hP, hg']
      · by_cases h3 : l = 2
        · simp only [h3, show (2 : ℤ) ≠ 1 by decide, show (2 : ℤ) ≠ -1 by decide, or_self,
            ite_false, ite_true, hQ]
        · simp only [h1, h2, h3, or_self, ite_false, rowsMatrix_mulRows, hQ, hh', matJ_mul]
  have := rowsMatrix_foldl_mulRows (fun l => if l = 1 ∨ l = -1 then P else if l = 2 then Q else
    mulRows Q Q) (pairLetters g h) hL w idRows
  rw [rowsMatrix_idRows, one_mul] at this
  exact this

@[expose] noncomputable def x1J : J := wordG (pairLetters a b) (abWord x1Str)

@[expose] noncomputable def x2J : J := wordG (pairLetters a b) (abWord x2Str)

@[expose] noncomputable def zJ : J := (x1J * x2J) ^ 9

theorem smul_val (g : J) (p : Fin nX) : (g • p).val = idx nX g p.val := (idx_val g p).symm

theorem rowsMatrix_seedB : rowsMatrix (rowsOf seedB) = matJ b := by
  rw [rowsMatrix_rowsOf_seedB, matJ, b_val]

section Facts


end Facts

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
