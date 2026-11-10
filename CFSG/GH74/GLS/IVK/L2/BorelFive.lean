module

public import CFSG.GH74.GLS.IVK.L2.BorelStd

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG.PSL2Table
open scoped MatrixGroups Pointwise

namespace L2Borel

section Conj

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K]

@[expose] noncomputable def eConj (e : K ≃* L2 F) (c : PSL(2, F)) : K ≃* L2 F :=
  ((toPSL e).trans (MulAut.conj c⁻¹)).trans (L2.equivPSL F).symm

omit [Finite F] in
theorem toPSL_eConj (e : K ≃* L2 F) (c : PSL(2, F)) (k : K) :
    toPSL (eConj e c) k = c⁻¹ * toPSL e k * c := by
  simp [toPSL, eConj]


theorem exists_isStd {p n : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ n) [Finite K]
    (e : K ≃* L2 F) (W : Sylow p K) :
    ∃ c : PSL(2, F), IsStd (eConj e c) (W : Subgroup K) ∧
      (W : Subgroup K) = (unipotent F).map (psiEquiv e c).toMonoidHom := by
  obtain ⟨c, hc⟩ := exists_psiEquiv_eq e hp hF W
  refine ⟨c, fun k => ?_, hc⟩
  rw [toPSL_eConj, hc, Subgroup.mem_map_equiv, psiEquiv_symm_apply]


end Conj

end L2Borel

open L2Borel


end CFSG.GH74.GLS.IVK
