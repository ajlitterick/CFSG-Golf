module

public import CFSG.Quasithin.AppendixH.H9.ModelBasic
public import CFSG.Quasithin.AppendixH.H9.ConjTransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

variable {n : ℕ}

@[expose] def ez (m : ℕ) : Fin (m + 1) → ZMod 2 := Pi.single 0 1


@[expose] def revGL (n : ℕ) : GL (Fin n) (ZMod 2) where
  val := Matrix.of fun i j => if j = Fin.rev i then 1 else 0
  inv := Matrix.of fun i j => if j = Fin.rev i then 1 else 0
  val_inv := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single (Fin.rev i)]
    · simp [Fin.rev_rev, eq_comm]
    · intro j _ hj; simp [hj]
    · simp
  inv_val := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single (Fin.rev i)]
    · simp [Fin.rev_rev, eq_comm]
    · intro j _ hj; simp [hj]
    · simp

@[expose] def utriGL (n : ℕ) : Subgroup (GL (Fin n) (ZMod 2)) :=
  (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular n (ZMod 2)).map
    (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* GL (Fin n) (ZMod 2))

@[expose] noncomputable def T0 (n : ℕ) : Subgroup (MulAut (PairN n)) :=
  (utriGL n).map (pairActN n) ⊔ Subgroup.zpowers (pairActN n (revGL n) * swapN n)


end CFSG.ASVolI.ChH
