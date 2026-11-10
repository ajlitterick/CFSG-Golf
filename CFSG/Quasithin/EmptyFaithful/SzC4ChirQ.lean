module

public import CFSG.Quasithin.EmptyFaithful.SzC4ChirLayer
public import CFSG.Quasithin.EmptyFaithful.SBd5UL
public import CFSG.Quasithin.MS93.ASC134

public section

namespace CFSG.Quasithin.SzC4

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem chiMat_dual (A : ChiAPI) {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    (x : Matrix.GeneralLinearGroup (Fin 3) F) (h7 : x ^ 7 = 1) :
    A.chiMat (moduleAct true x) = - A.chiMat (moduleAct false x) := by
  have hB7 : (moduleAct false x) ^ 7 = 1 := by
    unfold moduleAct
    simp only [Bool.false_eq_true, ite_false]
    rw [← Units.val_pow_eq_pow_val, h7]
    simp
  have hinv : ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((x : Matrix (Fin 3) (Fin 3) F)) ^ 6 := by
    have : x⁻¹ = x ^ 6 := by
      rw [inv_eq_iff_mul_eq_one, ← h7]
      group
    rw [this, Units.val_pow_eq_pow_val]
  have := A.chiMat_inv_transpose hF (moduleAct false x) hB7
  unfold moduleAct at this ⊢
  simp only [Bool.false_eq_true, ite_false, ite_true] at this ⊢
  rw [hinv]
  exact this


end CFSG.Quasithin.SzC4
