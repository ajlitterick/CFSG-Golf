
module

public import CFSG.Sporadic.ThSchreier.UASpaceBase

public import CFSG.Sporadic.ThSchreier.CentralizerData
public meta import CFSG.Sporadic.ThSchreier.CentralizerData
public meta import CFSG.Sporadic.ThSchreier.WordsBase1
public import Certificates.Certificate2325

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

private theorem native_ua_facts :
    eqRows (mulRows (mulRows rowsUAP rowsAmI) rowsUAQ) rowsD120 = true ∧
    eqRows (mulRows rowsUAPInv rowsUAP) idRows = true ∧
    eqRows (mulRows rowsUAQ rowsUAQInv) idRows = true ∧
    (∀ n ∈ uaRowsTxt, n < 2 ^ 248) ∧ uaRowsTxt.length = 4 * 248 :=
  Certificates.certificate2325


theorem rowsMatrix_rowsAmI : rowsMatrix rowsAmI = toMat a - 1 := by
  ext i j
  have hA : rowsMatrix rowsA = toMat a := isRows_a.eq
  rw [rowsMatrix_apply, Matrix.sub_apply, ← hA, rowsMatrix_apply, ← rowsMatrix_idRows,
    rowsMatrix_apply]
  simp only [rowsAmI, Array.getElem?_ofFn, Fin.is_lt, ↓reduceDIte, Option.getD_some]
  rw [V4.toVec_xor, Pi.add_apply, zmod2_sub_eq_add]
  have h1 : rowsA[i.val]? = some rowsA[i.val]! := by
    rw [Array.getElem?_eq_getElem (by rw [isRows_a.size]; exact i.isLt)]
    simp [getElem!_def, Array.getElem?_eq_getElem (by rw [isRows_a.size]; exact i.isLt)]
  have h2 : idRows[i.val]? = some idRows[i.val]! := by
    rw [Array.getElem?_eq_getElem (by rw [idRows_size]; exact i.isLt)]
    simp [getElem!_def, Array.getElem?_eq_getElem (by rw [idRows_size]; exact i.isLt)]
  rw [h1, h2]
  rfl

theorem ua_factor : matUAP * (toMat a - 1) * matUAQ = matD120 := by
  have h := rowsMatrix_eq_of_eqRows native_ua_facts.1
  rwa [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_rowsAmI, rowsMatrix_rowsD120] at h

theorem ua_P_inv : rowsMatrix rowsUAPInv * matUAP = 1 := by
  have h := rowsMatrix_eq_of_eqRows native_ua_facts.2.1
  rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at h

theorem ua_Q_inv : matUAQ * rowsMatrix rowsUAQInv = 1 := by
  have h := rowsMatrix_eq_of_eqRows native_ua_facts.2.2.1
  rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at h

theorem AmI_mul_Q : (toMat a - 1) * matUAQ = rowsMatrix rowsUAPInv * matD120 := by
  rw [← ua_factor, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ua_P_inv, Matrix.one_mul]

theorem P_mul_AmI : matUAP * (toMat a - 1) = matD120 * rowsMatrix rowsUAQInv := by
  rw [← ua_factor, Matrix.mul_assoc _ matUAQ, ua_Q_inv, Matrix.mul_one]

theorem mem_planeUA_iff (r : RowV) :
    r ∈ planeUA ↔ ∀ k : Fin 248, 120 ≤ k.val → Matrix.vecMul (ofRow r) matUAQ k = 0 := by
  constructor
  · rintro ⟨s, rfl⟩ k hk
    simp only [ofRow_toRow]
    rw [Matrix.vecMul_vecMul, AmI_mul_Q, ← Matrix.vecMul_vecMul, vecMul_matD120_apply,
      ite_eq_right (by omega)]
  · intro h
    have hproj : Matrix.vecMul (Matrix.vecMul (ofRow r) matUAQ) matD120 =
        Matrix.vecMul (ofRow r) matUAQ := by
      funext k
      rw [vecMul_matD120_apply]
      split_ifs with hk
      · rfl
      · exact (h k (by omega)).symm
    refine ⟨toRow (Matrix.vecMul (Matrix.vecMul (ofRow r) matUAQ) matUAP), ?_⟩
    simp only [ofRow_toRow]
    rw [Matrix.vecMul_vecMul, P_mul_AmI, ← Matrix.vecMul_vecMul, hproj, Matrix.vecMul_vecMul,
      ua_Q_inv, Matrix.vecMul_one]
    rfl


theorem inUA_iff (w : V4) : inUA w = true ↔ toRow w.toVec ∈ planeUA := by
  rw [mem_planeUA_iff, inUA, inUAT]
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true']
  have hvec := frApply_frTable_vecMul rowsUAQ w
  constructor
  · intro h k hk
    have := h k.val k.isLt
    rcases this with h1 | h1
    · omega
    · have h2 := congrFun hvec k
      rw [V4.toVec_apply, h1] at h2
      simp only [Bool.false_eq_true, ↓reduceIte] at h2
      exact h2.symm
  · intro h k hk
    by_cases hk' : k < 120
    · exact Or.inl hk'
    · right
      have h2 := congrFun hvec ⟨k, hk⟩
      rw [V4.toVec_apply] at h2
      have h3 := h ⟨k, hk⟩ (by simp; omega)
      simp only [ofRow_toRow] at h3
      rw [← h2] at h3
      cases hb : (frApply (frTable rowsUAQ) w).testBit k
      · rfl
      · rw [hb] at h3
        exact absurd h3 (by decide)

end CFSG.Sporadic.ThSchreier
