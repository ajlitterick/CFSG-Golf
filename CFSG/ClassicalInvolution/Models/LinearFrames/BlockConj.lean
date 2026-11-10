module

public import CFSG.ClassicalInvolution.Models.LinearFrames.Signs
public import CFSG.ClassicalInvolution.Phan.Torus

public section

namespace CFSG.ClassicalInvolution.Models

open Matrix
open CFSG.ClassicalInvolution.Phan (blockMat blockIdx blockMat_apply rotMat
  diagonal_mul_blockMat_mul_diagonal)

variable {K : Type} [Field K] {n : ℕ}

theorem diagonal_conj_blockMat_two (hn : 2 ≤ n) {d : Fin n → K} (hd : ∀ a, d a * d a = 1)
    (A : Matrix (Fin 2) (Fin 2) K) :
    Matrix.diagonal d * blockMat n 0 A * Matrix.diagonal d =
      blockMat n 0 (Matrix.diagonal ![d ⟨0, by omega⟩, d ⟨1, by omega⟩] * A *
        Matrix.diagonal ![d ⟨0, by omega⟩, d ⟨1, by omega⟩]) := by
  rw [diagonal_mul_blockMat_mul_diagonal (by omega : 0 + 2 ≤ n) d d hd]
  have hdd : (fun x : Fin 2 => d (blockIdx 0 (by omega : 0 + 2 ≤ n) x)) =
      ![d ⟨0, by omega⟩, d ⟨1, by omega⟩] := by
    funext x
    fin_cases x <;> rfl
  rw [hdd]


@[expose] def signUnit (x : K) (hx : x * x = 1) : Kˣ := ⟨x, x, hx, hx⟩


end CFSG.ClassicalInvolution.Models
