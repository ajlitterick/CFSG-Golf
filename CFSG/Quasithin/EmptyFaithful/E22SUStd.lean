module

public import CFSG.Quasithin.EmptyFaithful.E22SUGen
public import CFSG.Quasithin.EmptyFaithful.E22SULift

public section

namespace CFSG.Quasithin.E22S

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.Open
open scoped Matrix

variable {K : Type} [Field K] {p f : ℕ}

abbrev PSU3 (p f : ℕ) (K : Type) [Field K] : Type := StatedProj (unitarySU p f K 3)

@[expose] noncomputable def suMk (hU : UnitaryFieldData p f K) (M : Matrix (Fin 3) (Fin 3) K)
    (hdet : M.det = 1) (hu : (M.map hU.bar)ᵀ * M = 1) : ↥(unitarySU p f K 3) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero),
    (mem_unitarySU_iff hU).mpr ⟨by simpa using hdet, by simpa using hu⟩⟩


@[expose] def matZ (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![-1, 0, 0; 0, -1, 0; 0, 0, 1]


theorem det_matZ : (matZ K).det = 1 := by simp [matZ, Matrix.det_fin_three]


theorem bar_matZ (hU : UnitaryFieldData p f K) : (matZ K).map hU.bar = matZ K := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matZ]


theorem matZ_mul_self : matZ K * matZ K = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matZ, Matrix.mul_apply, Fin.sum_univ_three]


theorem matZ_transpose : (matZ K)ᵀ = matZ K := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matZ]


@[expose] noncomputable def zS (hU : UnitaryFieldData p f K) : ↥(unitarySU p f K 3) :=
  suMk hU (matZ K) det_matZ (by rw [bar_matZ, matZ_transpose, matZ_mul_self])


end CFSG.Quasithin.E22S
