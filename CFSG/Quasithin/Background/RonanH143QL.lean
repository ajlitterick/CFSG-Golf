module

public import CFSG.Quasithin.Background.RonanH143Data
public import CFSG.Quasithin.Background.RonanH143Gen
public import CFSG.Quasithin.Background.RonanH143Orb

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin

theorem smul_Qstd_of_perm {g : P24} (σ : Equiv.Perm (Fin 5)) (h : ∀ i, g • Zq i = Zq (σ i)) :
    g • Qstd = Qstd := by
  ext X
  rw [Finset.mem_smul_finset]
  constructor
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨i, rfl⟩ := (mem_Qstd_iff T).1 hT
    exact (mem_Qstd_iff _).2 ⟨σ i, (h i).symm⟩
  · intro hX
    obtain ⟨j, rfl⟩ := (mem_Qstd_iff X).1 hX
    refine ⟨Zq (σ.symm j), (mem_Qstd_iff _).2 ⟨_, rfl⟩, ?_⟩
    rw [h, Equiv.apply_symm_apply]

theorem exists_Zq_of_smul_Qstd {g : P24} (hg : g • Qstd = Qstd) (i : Fin 5) :
    ∃ j, g • Zq i = Zq j := by
  have hmem : g • Zq i ∈ Qstd := by
    rw [← hg]
    exact Finset.smul_mem_smul_finset ((mem_Qstd_iff _).2 ⟨i, rfl⟩)
  obtain ⟨j, hj⟩ := (mem_Qstd_iff _).1 hmem
  exact ⟨j, hj.symm⟩

theorem mem_Bstd_iff (x : Fin 24) : x ∈ Bstd ↔ ∀ i, x ∉ Zq i := by
  revert x
  decide +kernel

theorem smul_Bstd_of_smul_Qstd {g : P24} (hg : g • Qstd = Qstd) : g • Bstd = Bstd := by
  have hg' : g⁻¹ • Qstd = Qstd := by
    rw [inv_smul_eq_iff]
    exact hg.symm
  have hsub : g • Bstd ⊆ Bstd := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.1 hy
    rw [mem_Bstd_iff] at hx ⊢
    intro j hj
    obtain ⟨k, hk⟩ := exists_Zq_of_smul_Qstd hg' j
    have hmem : g⁻¹ • (g • x) ∈ g⁻¹ • Zq j := Finset.smul_mem_smul_finset hj
    rw [inv_smul_smul, hk] at hmem
    exact hx k hmem
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_smul_finset])

theorem mem_MY_iff {Γ : Subgroup P24} {α : Type*} [MulAction P24 α] {Y : α} {g : P24} :
    g ∈ MY Γ Y ↔ g ∈ Γ ∧ g • Y = Y := by
  simp [MY, MulAction.mem_stabilizer_iff]

theorem card_inf_stabilizer_eq {Γ : Subgroup P24} {α : Type*} [MulAction P24 α] (x : α) :
    Nat.card ↥(Γ ⊓ MulAction.stabilizer P24 x) = Nat.card ↥(MulAction.stabilizer ↥Γ x) := by
  have h : (Γ ⊓ MulAction.stabilizer P24 x).subgroupOf Γ = MulAction.stabilizer ↥Γ x := by
    ext g
    simp [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
  rw [← h]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm

theorem MY_Q_le_stab_B (Γ : Subgroup P24) :
    MY Γ Qstd ≤ Γ ⊓ MulAction.stabilizer P24 Bstd := by
  intro g hg
  rw [mem_MY_iff] at hg
  exact ⟨hg.1, MulAction.mem_stabilizer_iff.2 (smul_Bstd_of_smul_Qstd hg.2)⟩


theorem exists_piQ (Γ : Subgroup P24) :
    ∃ π : ↥(MY Γ Qstd) →* Equiv.Perm (Fin 5),
      ∀ (g : ↥(MY Γ Qstd)) (i : Fin 5), Zq (π g i) = (g : P24) • Zq i :=
  exists_labAct Zq Zq_injective (MY Γ Qstd) fun g hg i =>
    exists_Zq_of_smul_Qstd (mem_MY_iff.1 hg).2 i

noncomputable def piQ (Γ : Subgroup P24) : ↥(MY Γ Qstd) →* Equiv.Perm (Fin 5) :=
  Classical.choose (exists_piQ Γ)

theorem piQ_spec (Γ : Subgroup P24) (g : ↥(MY Γ Qstd)) (i : Fin 5) :
    Zq (piQ Γ g i) = (g : P24) • Zq i :=
  Classical.choose_spec (exists_piQ Γ) g i

theorem piQ_eq_of_smul {Γ : Subgroup P24} (g : ↥(MY Γ Qstd)) (σ : Equiv.Perm (Fin 5))
    (h : ∀ i, (g : P24) • Zq i = Zq (σ i)) : piQ Γ g = σ :=
  labAct_eq_of_smul Zq Zq_injective (MY Γ Qstd) (piQ Γ) (piQ_spec Γ) g σ h

theorem mem_MY_Q_of_perm {Γ : Subgroup P24} {g : P24} (hg : g ∈ Γ) (σ : Equiv.Perm (Fin 5))
    (h : ∀ i, g • Zq i = Zq (σ i)) : g ∈ MY Γ Qstd :=
  mem_MY_iff.2 ⟨hg, smul_Qstd_of_perm σ h⟩

theorem g1Perm_mem_MY {Γ : Subgroup P24} (hg : g1Perm ∈ Γ) : g1Perm ∈ MY Γ Qstd :=
  mem_MY_Q_of_perm hg sig1 g1_smul_Zq

theorem g2Perm_mem_MY {Γ : Subgroup P24} (hg : g2Perm ∈ Γ) : g2Perm ∈ MY Γ Qstd :=
  mem_MY_Q_of_perm hg sig2 g2_smul_Zq


theorem g2Perm_mem_mog22 : g2Perm ∈ mog22 := PO_le_mog22 g2Perm_mem_PO


theorem piQ_range_top {Γ : Subgroup P24} (h1 : g1Perm ∈ Γ) (h2 : g2Perm ∈ Γ) :
    (piQ Γ).range = ⊤ := by
  have hm := map_closure_eq_top_of_cycle_swap (piQ Γ) sig1 sig1_isCycle sig1_support 3
    ⟨g1Perm, g1Perm_mem_MY h1⟩ ⟨g2Perm, g2Perm_mem_MY h2⟩
    (piQ_eq_of_smul _ _ g1_smul_Zq) (by rw [← sig2_eq]; exact piQ_eq_of_smul _ _ g2_smul_Zq)
  exact eq_top_iff.2 (hm ▸ Subgroup.map_le_range _ _)

theorem ker_piQ_of_card {Γ : Subgroup P24} (h1 : g1Perm ∈ Γ) (h2 : g2Perm ∈ Γ) (N : Subgroup P24)
    (hN : N ≤ MY Γ Qstd) (hfix : ∀ g ∈ N, ∀ i, g • Zq i = Zq i)
    (hc : Nat.card ↥(MY Γ Qstd) ≤ Nat.card ↥N * 120) :
    (piQ Γ).ker = N.subgroupOf (MY Γ Qstd) := by
  refine ker_eq_of_card_le (piQ Γ) (piQ_range_top h1 h2) _ ?_ ?_
  · intro g hg
    rw [MonoidHom.mem_ker]
    refine piQ_eq_of_smul g 1 fun i => ?_
    rw [Equiv.Perm.coe_one, id_eq]
    exact hfix _ (Subgroup.mem_subgroupOf.1 hg) i
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv]
    have h5 : Nat.factorial 5 = 120 := by decide
    rw [h5]
    exact hc


end CFSG.Quasithin.RonanH143
