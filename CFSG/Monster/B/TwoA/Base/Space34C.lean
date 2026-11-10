
module

public import CFSG.Monster.B.TwoA.Base.Space34CBase

public import CFSG.Monster.B.TwoA.Base.Space34B
public import CFSG.Monster.B.TwoA.Base.Plane

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Sporadic.Mathieu

open scoped Pointwise

theorem alpha23K_gen4 :
    ∀ i : Fin 4, wAct v0 alpha23K (gen4 i) ∈ U4 := by
  intro i
  have hmem : ∀ j : Fin 4, gen4 j ∈ U4 := fun j => Submodule.subset_span ⟨j, rfl⟩
  fin_cases i
  · change wAct v0 alpha23K wFr ∈ U4
    rw [alpha23K_wFr]
    exact U4.add_mem (hmem 0) (hmem 1)
  · change wAct v0 alpha23K sW ∈ U4
    rw [alpha23K_sW]
    exact hmem 1
  · change wAct v0 alpha23K (pairW 4 5 offPair45 0) ∈ U4
    rw [pairW45_eq_decW, alpha23K, wAct_alpha_decW,
      show Native.actD 22 (genQuotMatrix 23) 49152 = 49152 by decide +kernel, ← pairW45_eq_decW]
    exact hmem 2
  · change wAct v0 alpha23K (pairW 8 9 offPair89 0) ∈ U4
    rw [pairW89_eq_decW, alpha23K, wAct_alpha_decW,
      show Native.actD 22 (genQuotMatrix 23) 393216 = 393216 by decide +kernel,
      ← pairW89_eq_decW]
    exact hmem 3

theorem alpha23K_gen3 :
    ∀ i : Fin 3, wAct v0 alpha23K (gen3 i) ∈ U3 := by
  intro i
  have hmem : ∀ j : Fin 3, gen3 j ∈ U3 := fun j => Submodule.subset_span ⟨j, rfl⟩
  fin_cases i
  · change wAct v0 alpha23K wFr ∈ U3
    rw [alpha23K_wFr]
    exact U3.add_mem (hmem 0) (hmem 1)
  · change wAct v0 alpha23K sW ∈ U3
    rw [alpha23K_sW]
    exact hmem 1
  · change wAct v0 alpha23K (pairW 4 5 offPair45 0) ∈ U3
    rw [pairW45_eq_decW, alpha23K, wAct_alpha_decW,
      show Native.actD 22 (genQuotMatrix 23) 49152 = 49152 by decide +kernel, ← pairW45_eq_decW]
    exact hmem 2

theorem alpha23K_mem_N4 :
    alpha23K ∈ wSetStab U4 := mem_wSetStab_span alpha23K_gen4

theorem alpha23K_mem_N3 :
    alpha23K ∈ wSetStab U3 := mem_wSetStab_span alpha23K_gen3

theorem monomial_mem_N4
    {p : AutPerm} (hp : p ∈ FA3) {a : C}
    (hk : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0) :
    (⟨_, hk⟩ : Kstab v0) ∈ wSetStab U4 :=
  (monomial_mem_wSetStab_iff pairSpace_U4 hk).2 hp.2

theorem monomial_mem_N3
    {p : AutPerm} (hp : p ∈ FA2) {a : C}
    (hk : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0) :
    (⟨_, hk⟩ : Kstab v0) ∈ wSetStab U3 :=
  (monomial_mem_wSetStab_iff pairSpace_U3 hk).2 hp.2

theorem N4_transitive :
    ∀ y ∈ U4, y ≠ 0 → ∃ k ∈ wSetStab U4, wAct v0 k wFr = y := by
  intro y hy hy0
  rcases (pairSpace_U4.mem_iff y).1 hy with rfl | rfl | ⟨x, x', h, hD, b, rfl⟩
  · exact absurd rfl hy0
  · exact ⟨1, (wSetStab U4).one_mem, by rw [wAct_one, Module.End.one_apply]⟩
  · obtain ⟨i, hi⟩ := A3_eq_duad7 _ hD
    have hpF : ((wordF3 i : FA3) : AutPerm) ∈ FA3 := (wordF3 i).2
    obtain ⟨hk, hmove⟩ := monomial_move (FA3_le_Ppair hpF) (offPair7 i) (wordF3_pair i) b
    have hm : (⟨_, hk⟩ : Kstab v0) ∈ wSetStab U4 := monomial_mem_N4 hpF hk
    refine ⟨_, (wSetStab U4).mul_mem alpha23K_mem_N4 hm, ?_⟩
    rw [wAct_mul, Module.End.mul_apply, alpha23K_wFr, hmove, pairW_of_duad_eq h hi]

theorem N3_transitive :
    ∀ y ∈ U3, y ≠ 0 → ∃ k ∈ wSetStab U3, wAct v0 k wFr = y := by
  intro y hy hy0
  rcases (pairSpace_U3.mem_iff y).1 hy with rfl | rfl | ⟨x, x', h, hD, b, rfl⟩
  · exact absurd rfl hy0
  · exact ⟨1, (wSetStab U3).one_mem, by rw [wAct_one, Module.End.one_apply]⟩
  · obtain ⟨i, hi3, hi⟩ := A2_eq_duad7 _ hD
    have hpair := wordF2_pair ⟨i, hi3⟩
    have hpF : ((wordF2 ⟨i, hi3⟩ : FA2) : AutPerm) ∈ FA2 := (wordF2 ⟨i, hi3⟩).2
    obtain ⟨hk, hmove⟩ := monomial_move (FA2_le_Ppair hpF) (offPair7 i) hpair b
    have hm : (⟨_, hk⟩ : Kstab v0) ∈ wSetStab U3 := monomial_mem_N3 hpF hk
    refine ⟨_, (wSetStab U3).mul_mem alpha23K_mem_N3 hm, ?_⟩
    rw [wAct_mul, Module.End.mul_apply, alpha23K_wFr, hmove, pairW_of_duad_eq h hi]

attribute [local instance] usharpAction

theorem natCard_U4 :
    Nat.card U4 = 16 := by
  rw [← FiniteField.pow_finrank_eq_natCard 2 U4, finrank_U4]
  rfl

theorem natCard_U3 :
    Nat.card U3 = 8 := by
  rw [← FiniteField.pow_finrank_eq_natCard 2 U3, finrank_U3]
  rfl

theorem natCard_N4 :
    Nat.card (wSetStab U4) = 41287680 := by
  have h := ((wSetStab U4 ⊓ Mfr).subgroupOf (wSetStab U4)).card_mul_index
  rw [index_wSetStab_inf_Mfr pairSpace_U4.wFr_mem N4_transitive, natCard_U4,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      wSetStab U4 ⊓ Mfr ≤ wSetStab U4)).toEquiv, natCard_NU4w] at h
  rw [← h]

theorem natCard_N3 :
    Nat.card (wSetStab U3) = 5505024 := by
  have h := ((wSetStab U3 ⊓ Mfr).subgroupOf (wSetStab U3)).card_mul_index
  rw [index_wSetStab_inf_Mfr pairSpace_U3.wFr_mem N3_transitive, natCard_U3,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      wSetStab U3 ⊓ Mfr ≤ wSetStab U3)).toEquiv, natCard_NU3w] at h
  rw [← h]

@[expose] def basisU4 :
    Module.Basis (Fin 4) (ZMod 2) U4 := Module.Basis.span linearIndependent_gen4

@[expose] def basisU3 :
    Module.Basis (Fin 3) (ZMod 2) U3 := Module.Basis.span linearIndependent_gen3

@[expose] def glU4Equiv :
    (Module.End (ZMod 2) U4)ˣ ≃* GL (Fin 4) (ZMod 2) :=
  Units.mapEquiv (LinearMap.toMatrixAlgEquiv basisU4).toMulEquiv

@[expose] def glU3Equiv :
    (Module.End (ZMod 2) U3)ˣ ≃* GL (Fin 3) (ZMod 2) :=
  Units.mapEquiv (LinearMap.toMatrixAlgEquiv basisU3).toMulEquiv


instance finite_glU4 :
    Finite (Module.End (ZMod 2) U4)ˣ :=
  Finite.of_equiv _ glU4Equiv.symm.toEquiv

instance finite_glU3 :
    Finite (Module.End (ZMod 2) U3)ˣ :=
  Finite.of_equiv _ glU3Equiv.symm.toEquiv


end CFSG.Monster.B.TwoA
