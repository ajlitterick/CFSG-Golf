module

public import CFSG.ClassicalInvolution.Balance.StrongPowDiagGlue
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagLinear
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagUnitary
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagSp

public section

namespace CFSG.ClassicalInvolution.Balance.BootRank3

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance.StrongBalance
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

section Transport

variable {K K' X : Type*} [Group K] [Group K'] [Group X]

theorem range_comp_symm (ε : K ≃* K') (ψ : K →* X) :
    (ψ.comp ε.symm.toMonoidHom).range = ψ.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ε.symm.surjective,
    ← MonoidHom.range_eq_map]

theorem ker_comp_symm_le_center (ε : K ≃* K') (ψ : K →* X) (hker : ψ.ker ≤ Subgroup.center K) :
    (ψ.comp ε.symm.toMonoidHom).ker ≤ Subgroup.center K' := by
  intro x hx
  have h1 : ε.symm x ∈ Subgroup.center K := hker (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx))
  rw [Subgroup.mem_center_iff] at h1 ⊢
  intro y
  apply ε.symm.injective
  rw [map_mul, map_mul]
  exact h1 (ε.symm y)

end Transport


end CFSG.ClassicalInvolution.Balance.BootRank3
