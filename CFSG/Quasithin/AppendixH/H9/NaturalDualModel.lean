module

public import CFSG.Milestones.ASVolI.H6

public section

open scoped commutatorElement Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

abbrev PairN (n : ℕ) : Type := Multiplicative (Fin n → ZMod 2) × Multiplicative (Fin n → ZMod 2)

@[expose] def dualGLn (n : ℕ) (g : GL (Fin n) (ZMod 2)) : GL (Fin n) (ZMod 2) where
  val := ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ
  inv := (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ
  val_inv := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one]
  inv_val := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]

@[expose] def dualHomN (n : ℕ) : GL (Fin n) (ZMod 2) →* GL (Fin n) (ZMod 2) where
  toFun := dualGLn n
  map_one' := Units.ext (by
    show (((1 : GL (Fin n) (ZMod 2))⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = 1
    rw [inv_one, Units.val_one, Matrix.transpose_one])
  map_mul' g h := Units.ext (by
    show (((g * h)⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ =
      ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *
        ((h⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ
    rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul])

@[expose] noncomputable def pairActN (n : ℕ) : GL (Fin n) (ZMod 2) →* MulAut (PairN n) :=
  prodAct (natHom n (ZMod 2)) ((natHom n (ZMod 2)).comp (dualHomN n))

@[expose] noncomputable def Lg (n : ℕ) : Subgroup (MulAut (PairN n)) := (pairActN n).range

@[expose] def swapN (n : ℕ) : MulAut (PairN n) := MulEquiv.prodComm

@[expose] noncomputable def Mg (n : ℕ) : Subgroup (MulAut (PairN n)) := Lg n ⊔ Subgroup.zpowers (swapN n)


end CFSG.ASVolI.ChH
