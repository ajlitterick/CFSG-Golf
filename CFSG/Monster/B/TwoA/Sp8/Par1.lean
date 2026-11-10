
module

public import CFSG.Monster.B.TwoA.Sp8.Par1Base

public import CFSG.Monster.B.TwoA.Unitary.Semilinear

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.B.TwoA

theorem xhat_mem_A8 : xhat ∈ A8 := B7_le_A8 (gen_mem_B7 (by simp))

theorem cQ_ne_one :
    cQ ≠ 1 := fun h => cQ_not_mem_A8 (h ▸ A8.one_mem)

theorem cQ_ne_xhat :
    cQ ≠ xhat := fun h => cQ_not_mem_A8 (h ▸ xhat_mem_A8)

theorem sigmaW_ne_zero :
    Unitary.sigmaW ≠ 0 := by
  intro h
  rcases (psiW_eq_zero_iff cE).1 (psiW_cE.trans h) with h1 | h1
  · exact cQ_ne_one (congrArg Subtype.val h1)
  · exact cQ_ne_xhat (congrArg Subtype.val h1)

theorem finrank_sigLine :
    Module.finrank (ZMod 2) sigLine = 1 :=
  finrank_span_singleton sigmaW_ne_zero

theorem natCard_N1 :
    Nat.card N1 = 2 ^ 22 := by
  rw [N1_eq]
  have h := natCard_Ehat_inf_centralizer_EU (U := sigLine)
  rw [finrank_sigLine] at h
  exact h.trans (by norm_num)

theorem pCore_Usig :
    CFSG.pCore 2 Unitary.Usig = ⊥ := by
  let _ : MulAction Unitary.Usig (Fin 891) := Unitary.natAction
  have : FaithfulSMul Unitary.Usig (Fin 891) :=
    ⟨fun {u u'} h => Unitary.rhoN_injective (Equiv.ext fun j => h j)⟩
  have : MulAction.IsPretransitive Unitary.Usig (Fin 891) := ⟨fun i j => by
    obtain ⟨u, hu, h⟩ := Unitary.transitive_n6vec i j
    refine ⟨(⟨u, hu⟩ : Unitary.Usig)⁻¹, ?_⟩
    apply Unitary.n6vec_injective
    change Unitary.n6vec (Unitary.natIdx ((⟨u, hu⟩ : Unitary.Usig)⁻¹)⁻¹ i) = Unitary.n6vec j
    rw [inv_inv, Unitary.n6vec_natIdx]
    exact h⟩
  exact pCore_two_eq_bot_of_odd (X := Fin 891) (by rw [Nat.card_fin]; exact ⟨445, by norm_num⟩)

theorem pCore_P1 :
    (CFSG.pCore 2 P1).map P1.subtype = N1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : IsPGroup 2 p1Proj.ker := by
    rw [ker_p1Proj]
    exact IsPGroup.of_card (n := 22)
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe N1_le_P1).toEquiv, natCard_N1])
  rw [← ker_eq_pCore_of_surjective p1Proj_surjective hker pCore_Usig, ker_p1Proj,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.2 N1_le_P1]

theorem nonempty_p1Quot_PSU62 :
    Nonempty (P1 ⧸ N1.subgroupOf P1 ≃* Unitary.PSU62) :=
  ⟨(p1QuotEquiv.trans Unitary.phiU).trans Unitary.thetaEquiv⟩

theorem natCard_P1 :
    Nat.card P1 = 77148607752437760 := by
  have h := natCard_ZU (U := sigLine)
  rw [finrank_sigLine, wFix_sigLine, Unitary.natCard_Usig] at h
  rw [P1_eq_ZU, h]
  norm_num


theorem exists_bV_orth :
    ∃ y ∈ bV.orthogonal sigLine, ∃ z ∈ bV.orthogonal sigLine,
    bV y z = 1 := by
  by_contra hne
  push Not at hne
  have hle : bV.orthogonal sigLine ≤ bV.orthogonal (bV.orthogonal sigLine) := by
    intro z hz
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    rcases zmod2_cases (bV y z) with h | h
    · exact h
    · exact absurd h (hne y hy z hz)
  rw [sigLine_orth_orth] at hle
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal bV_nondegenerate, Co2.finrank_W,
    finrank_sigLine] at h1
  omega

theorem commutator_N1 :
    commutator N1 = (Subgroup.zpowers xhat).subgroupOf N1 := by
  apply le_antisymm
  · rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    rw [Subgroup.mem_subgroupOf, commutatorElement_def]
    change (g : Dfull) * h * (g : Dfull)⁻¹ * (h : Dfull)⁻¹ ∈ Subgroup.zpowers xhat
    rw [Ehat_commutator (N1_le_Ehat g.2) (N1_le_Ehat h.2)]
    exact Subgroup.npow_mem_zpowers _ _
  · obtain ⟨y, hy, z, hz, hyz⟩ := exists_bV_orth
    obtain ⟨a, rfl, ha⟩ := exists_EU_of_mem hy
    obtain ⟨b, rfl, hb⟩ := exists_EU_of_mem hz
    rw [← N1_eq_EU] at ha hb
    have hx : xhat ∈ N1 := EU_sigLine_le_N1 xhat_mem_EU
    have hm := Subgroup.commutator_mem_commutator (Subgroup.mem_top (⟨a, ha⟩ : N1))
      (Subgroup.mem_top (⟨b, hb⟩ : N1))
    rw [commutatorElement_def] at hm
    have hab : (⟨a, ha⟩ : N1) * ⟨b, hb⟩ * (⟨a, ha⟩ : N1)⁻¹ * (⟨b, hb⟩ : N1)⁻¹ = ⟨xhat, hx⟩ := by
      apply Subtype.ext
      change (a : Dfull) * b * (a : Dfull)⁻¹ * (b : Dfull)⁻¹ = xhat
      rw [Ehat_commutator (N1_le_Ehat ha) (N1_le_Ehat hb)]
      change xhat ^ (bV (psiW a) (psiW b)).val = xhat
      rw [hyz, show (1 : ZMod 2).val = 1 from rfl, pow_one]
    rw [hab] at hm
    intro g hg
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff] at hg
    obtain ⟨k, hk⟩ := hg
    have hg' : g = (⟨xhat, hx⟩ : N1) ^ k := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hk.symm
    rw [hg', commutator_def]
    exact Subgroup.zpow_mem _ hm _


@[expose] def kleinHom :
    Multiplicative (ZMod 2 × ZMod 2) →* Dfull where
  toFun v := xhat ^ v.toAdd.1.val * cQ ^ v.toAdd.2.val
  map_one' := by
    show xhat ^ (0 : ZMod 2).val * cQ ^ (0 : ZMod 2).val = 1
    rw [ZMod.val_zero, pow_zero, pow_zero, mul_one]
  map_mul' v w := by
    show xhat ^ (v.toAdd.1 + w.toAdd.1).val * cQ ^ (v.toAdd.2 + w.toAdd.2).val =
      xhat ^ v.toAdd.1.val * cQ ^ v.toAdd.2.val * (xhat ^ w.toAdd.1.val * cQ ^ w.toAdd.2.val)
    have hc : Commute (cQ ^ v.toAdd.2.val) (xhat ^ w.toAdd.1.val) :=
      (show Commute xhat cQ from xhat_comm_cQ).symm.pow_pow _ _
    rw [xhat_pow_val_add, cQ_pow_add, mul_assoc, ← mul_assoc (xhat ^ w.toAdd.1.val),
      ← hc.eq, mul_assoc, mul_assoc]


theorem range_kleinHom :
    kleinHom.range = Subgroup.closure {xhat, cQ} := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ xhat_mem_closure _)
      (Subgroup.pow_mem _ cQ_mem_closure _)
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · refine ⟨Multiplicative.ofAdd (1, 0), ?_⟩
      show xhat ^ (1 : ZMod 2).val * cQ ^ (0 : ZMod 2).val = xhat
      rw [ZMod.val_zero, pow_zero, mul_one, show (1 : ZMod 2).val = 1 from rfl, pow_one]
    · refine ⟨Multiplicative.ofAdd (0, 1), ?_⟩
      show xhat ^ (0 : ZMod 2).val * cQ ^ (1 : ZMod 2).val = cQ
      rw [ZMod.val_zero, pow_zero, one_mul, show (1 : ZMod 2).val = 1 from rfl, pow_one]


end CFSG.Monster.B.TwoA.Sp8
