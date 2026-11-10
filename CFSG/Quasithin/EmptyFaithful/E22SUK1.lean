module

public import CFSG.Quasithin.EmptyFaithful.E22SQ
public import CFSG.Quasithin.EmptyFaithful.E22SUStd
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2
public import CFSG.Quasithin.EmptyFaithful.E22SUFrame

public section

namespace CFSG.Quasithin.E22S

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open scoped MatrixGroups Matrix

namespace UK1

section Matrices

variable {K : Type} [Field K]


end Matrices

section Stabilizer

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]


end Stabilizer

section Image

variable {K : Type} [Field K] {p f : ℕ}


end Image

section SL2

open CFSG.ClassicalInvolution

variable {F : Type*} [Field F] [Finite F] {P : Type*} [Group P]

omit [Finite F] in
theorem isSimpleGroup_quotient_center_of_equiv_sl2 (h4 : 4 ≤ Nat.card F) (e : P ≃* SL(2, F)) :
    IsSimpleGroup (P ⧸ Subgroup.center P) := by
  have : IsSimpleGroup (SL(2, F) ⧸ Subgroup.center SL(2, F)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have hmap : (Subgroup.center P).map e.toMonoidHom = Subgroup.center SL(2, F) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_center_iff_of_equiv_sl2 e x).mp hx
    · intro hy
      exact ⟨e.symm y, (mem_center_iff_of_equiv_sl2 e _).mpr (by simpa using hy), by simp⟩
  exact (QuotientGroup.congr (Subgroup.center P) (Subgroup.center SL(2, F)) e hmap).isSimpleGroup


end SL2

section Normalizer


end Normalizer

section Products


end Products

section Involutions


end Involutions

end UK1

open UK1


end CFSG.Quasithin.E22S
