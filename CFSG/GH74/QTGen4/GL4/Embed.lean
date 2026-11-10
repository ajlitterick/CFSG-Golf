module

public import CFSG.GH74.QTGen4.CharTwoQuotient

public section

namespace CFSG.GH74.QTGen4

open Matrix

variable {R : Type*} [Semiring R]

noncomputable def splitFour {d k : ℕ} (h : d + k = 4) : Fin 4 ≃ Fin d ⊕ Fin k :=
  (finCongr h.symm).trans finSumFinEquiv.symm

noncomputable def blockMatrix {d k : ℕ} (e : Fin 4 ≃ Fin d ⊕ Fin k) (A : Matrix (Fin d) (Fin d) R) :
    Matrix (Fin 4) (Fin 4) R :=
  (fromBlocks A 0 0 (1 : Matrix (Fin k) (Fin k) R)).submatrix e e

theorem blockMatrix_mul {d k : ℕ} (e : Fin 4 ≃ Fin d ⊕ Fin k) (A B : Matrix (Fin d) (Fin d) R) :
    blockMatrix e (A * B) = blockMatrix e A * blockMatrix e B := by
  simp [blockMatrix, fromBlocks_multiply]

theorem blockMatrix_one {d k : ℕ} (e : Fin 4 ≃ Fin d ⊕ Fin k) :
    blockMatrix e (1 : Matrix (Fin d) (Fin d) R) = 1 := by
  simp [blockMatrix, fromBlocks_one]

noncomputable def blockMatrixHom {d k : ℕ} (e : Fin 4 ≃ Fin d ⊕ Fin k) :
    Matrix (Fin d) (Fin d) R →* Matrix (Fin 4) (Fin 4) R where
  toFun := blockMatrix e
  map_one' := blockMatrix_one e
  map_mul' := blockMatrix_mul e

theorem blockMatrixHom_injective {d k : ℕ} (e : Fin 4 ≃ Fin d ⊕ Fin k) :
    Function.Injective (blockMatrixHom (R := R) e) := by
  intro A B h
  ext i j
  have h' := congrFun (congrFun h (e.symm (Sum.inl i))) (e.symm (Sum.inl j))
  simpa [blockMatrixHom, blockMatrix] using h'

noncomputable def blockGL {d k : ℕ} (e : Fin 4 ≃ Fin d ⊕ Fin k) :
    GL (Fin d) R →* GL (Fin 4) R :=
  Units.map (blockMatrixHom e)

theorem blockGL_injective {d k : ℕ} (e : Fin 4 ≃ Fin d ⊕ Fin k) :
    Function.Injective (blockGL (R := R) e) :=
  Units.map_injective (blockMatrixHom_injective e)


end CFSG.GH74.QTGen4
