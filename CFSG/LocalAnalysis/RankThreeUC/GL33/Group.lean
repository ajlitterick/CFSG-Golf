module

public import CFSG.LocalAnalysis.RankThreeUC.GL33.CodeSound
public import Certificates.Data.GL33.Check
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.GL33

open CFSG.GL33.Native

abbrev G := GL (Fin 3) (ZMod 3)

@[expose] def Good (c : ℕ) : Prop := (toM c).det ≠ 0

noncomputable def ofCode (c : ℕ) : G := by
  classical exact if h : Good c then Matrix.GeneralLinearGroup.mkOfDetNeZero (toM c) h else 1

private theorem digs_getElem (a : ℕ) {n : ℕ} (hn : n < 9) : (digs a)[n]! = dig a n := by
  simp [digs, dig, hn]

private theorem digs_ent (a : ℕ) {i j : ℕ} (hi : i < 3) (hj : j < 3) :
    (digs a)[3 * i + j]! = ent a i j := digs_getElem a (by omega)

theorem mulF_eq_mulC (a b : ℕ) : mulF a b = mulC a b := by
  dsimp only [mulF, mulC]
  congr 1
  refine List.map_congr_left fun k hk => ?_
  have hk9 : k < 9 := List.mem_range.1 hk
  have hi : k / 3 < 3 := by omega
  have hj : k % 3 < 3 := by omega
  have x0 : (digs a)[3 * (k / 3)]! = ent a (k / 3) 0 :=
    digs_ent a (i := k / 3) (j := 0) hi (by omega)
  have x1 : (digs a)[3 * (k / 3) + 1]! = ent a (k / 3) 1 :=
    digs_ent a (i := k / 3) (j := 1) hi (by omega)
  have x2 : (digs a)[3 * (k / 3) + 2]! = ent a (k / 3) 2 :=
    digs_ent a (i := k / 3) (j := 2) hi (by omega)
  have y0 : (digs b)[k % 3]! = ent b 0 (k % 3) := by
    simpa using digs_ent b (i := 0) (j := k % 3) (by omega) hj
  have y1 : (digs b)[3 + k % 3]! = ent b 1 (k % 3) := by
    simpa using digs_ent b (i := 1) (j := k % 3) (by omega) hj
  have y2 : (digs b)[6 + k % 3]! = ent b 2 (k % 3) := by
    simpa using digs_ent b (i := 2) (j := k % 3) (by omega) hj
  rw [x0, x1, x2, y0, y1, y2]

theorem good_oneC : Good oneC := by
  unfold Good
  rw [toM_oneC, Matrix.det_one]
  exact one_ne_zero

theorem good_mulF {a b : ℕ} (ha : Good a) (hb : Good b) : Good (mulF a b) := by
  unfold Good at *
  rw [mulF_eq_mulC, toM_mulC, Matrix.det_mul]
  exact mul_ne_zero ha hb

theorem coe_ofCode {c : ℕ} (hc : Good c) :
    ((ofCode c : G) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = toM c := by
  unfold ofCode
  rw [dif_pos hc]
  rfl

theorem ofCode_oneC : ofCode oneC = 1 := by
  apply Units.ext
  rw [coe_ofCode good_oneC, toM_oneC]
  rfl

theorem ofCode_mulF {a b : ℕ} (ha : Good a) (hb : Good b) :
    ofCode (mulF a b) = ofCode a * ofCode b := by
  apply Units.ext
  rw [coe_ofCode (good_mulF ha hb), mulF_eq_mulC, toM_mulC]
  rw [Units.val_mul, coe_ofCode ha, coe_ofCode hb]


theorem good_of_mem_glCodes {c : ℕ} (h : c ∈ glCodes ()) : Good c :=
  ((mem_glCodes_iff c).1 h).2

theorem encode_mem_glCodes (g : G) :
    encode (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ glCodes () :=
  (mem_glCodes_iff _).2 ⟨encode_lt _, by
    rw [toM_encode]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero⟩

theorem ofCode_encode (g : G) :
    ofCode (encode (g : Matrix (Fin 3) (Fin 3) (ZMod 3))) = g := by
  apply Units.ext
  rw [coe_ofCode (good_of_mem_glCodes (encode_mem_glCodes g)), toM_encode]

theorem ofCode_injOn {a b : ℕ} (ha : a ∈ glCodes ()) (hb : b ∈ glCodes ())
    (h : ofCode a = ofCode b) : a = b := by
  have ha' := (mem_glCodes_iff a).1 ha
  have hb' := (mem_glCodes_iff b).1 hb
  refine eq_of_toM_eq ha'.1 hb'.1 ?_
  rw [← coe_ofCode ha'.2, ← coe_ofCode hb'.2, h]


theorem card_G : Nat.card G = 11232 := by
  rw [Matrix.card_GL_field 3, ZMod.card, Fin.prod_univ_three]
  norm_num

@[expose] noncomputable def sub2 (a b : ℕ) : Subgroup G := Subgroup.closure {ofCode a, ofCode b}


theorem toM_minusOneC : toM minusOneC = -1 := by
  ext x y
  fin_cases x <;> fin_cases y <;> decide

theorem good_minusOneC : Good minusOneC := by
  unfold Good
  rw [toM_minusOneC, Matrix.det_neg, Matrix.det_one]
  decide

end CFSG.GL33

end
