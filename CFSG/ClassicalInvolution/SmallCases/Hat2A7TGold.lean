module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TightEnd
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TClique

public section

namespace CFSG.ClassicalInvolution.Hat2A7T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
open scoped Pointwise

section Sylow

variable {F : Type*} [Group F] [Finite F]

theorem exists_conj_mem_sylow (T : Sylow 2 F) {y : F} (hy : IsPGroup 2 (Subgroup.zpowers y)) :
    ∃ g : F, g * y * g⁻¹ ∈ (T : Subgroup F) := by
  obtain ⟨Q, hQ⟩ := hy.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq F Q T
  refine ⟨g, ?_⟩
  have h1 : y ∈ (Q : Subgroup F) := hQ (Subgroup.mem_zpowers y)
  have h2 : MulAut.conj g • y ∈ MulAut.conj g • (Q : Subgroup F) :=
    Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) _ h1
  rw [← Sylow.coe_subgroup_smul, hg] at h2
  simpa [MulAut.smul_def, MulAut.conj_apply] using h2


end Sylow

section Gold


end Gold

end CFSG.ClassicalInvolution.Hat2A7T
