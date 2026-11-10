module

public import CFSG.Quasithin.AppendixH.H9.SylowModel

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH.VectorStabilizer

variable {m : ℕ}


@[expose] def blockMat (r : Fin m → ZMod 2) (B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2) :=
  Matrix.of (Matrix.vecCons (Matrix.vecCons (1 : ZMod 2) r) fun i => Matrix.vecCons (0 : ZMod 2) (B i))

@[simp] theorem blockMat_zero_zero (r : Fin m → ZMod 2) (B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    blockMat r B 0 0 = 1 := by
  simp [blockMat]

@[simp] theorem blockMat_zero_succ (r : Fin m → ZMod 2) (B : Matrix (Fin m) (Fin m) (ZMod 2))
    (j : Fin m) : blockMat r B 0 j.succ = r j := by
  simp [blockMat]

@[simp] theorem blockMat_succ_zero (r : Fin m → ZMod 2) (B : Matrix (Fin m) (Fin m) (ZMod 2))
    (i : Fin m) : blockMat r B i.succ 0 = 0 := by
  simp [blockMat]

@[simp] theorem blockMat_succ_succ (r : Fin m → ZMod 2) (B : Matrix (Fin m) (Fin m) (ZMod 2))
    (i j : Fin m) : blockMat r B i.succ j.succ = B i j := by
  simp [blockMat]


@[expose] def blk (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) :
    Matrix (Fin m) (Fin m) (ZMod 2) :=
  Matrix.of fun i j => A i.succ j.succ

@[simp] theorem blk_apply (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) (i j : Fin m) :
    blk A i j = A i.succ j.succ := rfl

@[simp] theorem blk_blockMat (r : Fin m → ZMod 2) (B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    blk (blockMat r B) = B := by
  ext i j
  simp


end CFSG.ASVolI.ChH.VectorStabilizer
