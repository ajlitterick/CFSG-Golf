module

public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup
open scoped Pointwise

variable {X : Type*} [Group X]

theorem mem_conjugate_iff_conj_mem {H : Subgroup X} {g x : X} :
    x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  simpa [conjugate, MulAut.conj_symm_apply] using
    (mem_map_equiv (f := MulAut.conj g⁻¹) (K := H) (x := x))


end CFSG.ComponentClassification.UnbalancedGS
