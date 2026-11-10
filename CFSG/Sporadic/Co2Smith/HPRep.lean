module

public import CFSG.Sporadic.Co2Smith.HPModel

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open CFSG.Certificates.ExtraspecialNF
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem vecMulF_eq (Y : Array ℕ) (v : ℕ) : ∀ k j acc, j + k = 22 →
    Native.vecMulF Y v j acc =
      (List.range' j k).foldl (fun acc j => if v.testBit j then acc ^^^ (Y[j]?.getD 0) else acc)
        acc
  | 0, j, acc, h => by
    rw [Native.vecMulF, ite_eq_right (by omega)]
    rfl
  | k + 1, j, acc, h => by
    rw [Native.vecMulF, ite_eq_left (by omega), vecMulF_eq Y v k (j + 1) _ (by omega),
      List.range'_succ, List.foldl_cons]
    congr 1
    split_ifs
    · congr 1
      rw [getElem!_def]
      generalize Y[j]? = o
      cases o <;> rfl
    · rfl

theorem vecMulF_zero (Y : Array ℕ) (v : ℕ) : Native.vecMulF Y v 0 0 = vecMulN 22 Y v := by
  rw [vecMulF_eq Y v 22 0 0 rfl, vecMulN, List.range_eq_range']

theorem mulRowsF_eq (X Y : Array ℕ) : Native.mulRowsF X Y = mulRows 22 X Y := by
  rw [Native.mulRowsF, mulRows]
  congr 1
  funext v
  exact vecMulF_zero Y v

theorem sRowsF_eq (T : Array (Array (Array ℕ))) (n : ℕ) :
    Native.sRowsF T n = Native.sRowsN T n := by
  simp only [Native.sRowsF, Native.sRowsN, mulRowsF_eq]

@[expose] def RepOK
    (y : FibP) (a : Array ℕ × Array ℤ) : Prop :=
  Native.validM a.1 = true ∧ a.2.size = 64 ∧
    ((y.1.1 : Cz) : K).val.val = rowsMatrix 22 a.1 ∧
    (spinHom y.1.2 : Matrix (Fin 8) (Fin 8) ℤ) = toMatZ a.2

theorem size_mulZ (A B : Array ℤ) : (Native.mulZ A B).size = 64 := by
  simp [Native.mulZ]

theorem RepOK.mul
    {y y' : FibP} {a a' : Array ℕ × Array ℤ} (h : RepOK y a) (h' : RepOK y' a') :
    RepOK (y * y') (Native.mulP a a') := by
  refine ⟨?_, size_mulZ _ _, ?_, ?_⟩
  · rw [Native.mulP, mulRowsF_eq]
    exact validM_mulRows h.1 h'.1
  · show ((y.1.1 * y'.1.1 : Cz) : K).val.val = _
    rw [Native.mulP, mulRowsF_eq, rowsMatrix_mulRows, Subgroup.coe_mul, val_val_mul, h.2.2.1,
      h'.2.2.1]
  · show (spinHom (y.1.2 * y'.1.2) : Matrix (Fin 8) (Fin 8) ℤ) = _
    rw [map_mul, Units.val_mul, h.2.2.2, h'.2.2.2, Native.mulP, toMatZ_mulZ]

theorem toMatZ_injOn {X Y : Array ℤ} (hX : X.size = 64) (hY : Y.size = 64)
    (h : toMatZ X = toMatZ Y) : X = Y := by
  refine Array.ext (hX.trans hY.symm) fun t ht _ => ?_
  have h8 : t / 8 < 8 := by omega
  have := congrFun (congrFun h ⟨t / 8, h8⟩) ⟨t % 8, Nat.mod_lt _ (by norm_num)⟩
  simp only [toMatZ] at this
  rw [show 8 * (t / 8) + t % 8 = t by omega, getElem!_pos X t ht,
    getElem!_pos Y t (by omega)] at this
  exact this


theorem rows_z0 : z0.val.val = rowsMatrix 22 seedRowsArr[0]! := by
  rw [seedRowsArr_zero]
  exact z0_val


theorem RepOK.eq
    {y y' : FibP} {a : Array ℕ × Array ℤ} (h : RepOK y a) (h' : RepOK y' a) :
    y = y' := by
  have h1 : y.1.1 = y'.1.1 := Subtype.ext (eq_of_val_eq (h.2.2.1.trans h'.2.2.1.symm))
  have h2 : spinHom y.1.2 = spinHom y'.1.2 := Units.ext (h.2.2.2.trans h'.2.2.2.symm)
  have h3 : covMap y.1.2 = covMap y'.1.2 := by
    rw [← (SmithConfig.mem_fibSub _ _ _).mp y.2, ← (SmithConfig.mem_fibSub _ _ _).mp y'.2, h1]
  have h4 : y.1.2 = y'.1.2 := covMap_spinHom_injective (Prod.ext h3 h2)
  exact Subtype.ext (Prod.ext h1 h4)

theorem RepOK.unique
    {y : FibP} {a a' : Array ℕ × Array ℤ} (h : RepOK y a) (h' : RepOK y a') :
    a = a' :=
  Prod.ext (eq_of_rowsMatrix_eq h.1 h'.1 (h.2.2.1.symm.trans h'.2.2.1))
    (toMatZ_injOn h.2.1 h'.2.1 (h.2.2.2.symm.trans h'.2.2.2))


end CFSG.Sporadic.Co2Smith
