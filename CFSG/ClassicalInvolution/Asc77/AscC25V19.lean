module

public import CFSG.ClassicalInvolution.Asc77.AscC25V12
public import CFSG.ClassicalInvolution.Asc77.AscC25V18

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups commutatorElement

section Strong

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem fieldChar_eq_one_of_mem (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {k : G} (hk : k ∈ K)
    (hkN : k ∈ Subgroup.normalizer (K : Set G)) : fieldChar hp hq e ⟨k, hkN⟩ = 1 := by
  have h := normalizerToPGammaL2Mod_mem_range_inl_of_mem e (gf_facts hp hq).2.1
    (gf_facts hp hq).2.2.1 (gf_facts hp hq).2.2.2 hk hkN
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker] at h
  exact h


end Strong

section Main


end Main

end CFSG.ClassicalInvolution.Asc77.C25V
