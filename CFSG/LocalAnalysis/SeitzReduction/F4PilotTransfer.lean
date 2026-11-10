module

public import CFSG.LocalAnalysis.SeitzReduction.Endgame

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup

variable {G : Type*} [Group G] [Finite G]

private theorem not_dvd_index_of_unique {p : ℕ} [Fact p.Prime] {M : Subgroup G} {t : G}
    (htM : t ∈ M) (ht : IsPGroup p (zpowers t)) (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) :
    ¬ p ∣ M.index := by
  have hfix : MulAction.fixedPoints (zpowers t) (G ⧸ M) = {((1 : G) : G ⧸ M)} := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff, QuotientGroup.eq, mul_one]
      constructor
      · intro h
        have h1 : ((⟨t, mem_zpowers t⟩ : zpowers t) • (g : G ⧸ M)) = g := h _
        rw [Subgroup.mk_smul, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at h1
        have h2 : g⁻¹ * t * g ∈ M := by
          have := M.inv_mem h1
          simpa [mul_assoc] using this
        exact M.inv_mem (huniq g h2)
      · rintro h ⟨z, hz⟩
        have hzM : z ∈ M := zpowers_le.2 htM hz
        rw [Subgroup.mk_smul, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
        have hg : g ∈ M := by simpa using M.inv_mem h
        simpa [mul_assoc] using M.mul_mem (M.inv_mem hg) (M.mul_mem (M.inv_mem hzM) hg)
  have hone : Nat.card (MulAction.fixedPoints (zpowers t) (G ⧸ M)) = 1 := by
    rw [hfix]
    exact Nat.card_unique
  have hmod := ht.card_modEq_card_fixedPoints (G ⧸ M)
  rw [hone] at hmod
  intro hdvd
  have h1 : p ∣ 1 := (hmod.dvd_iff (dvd_refl p)).1 hdvd
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h1)

theorem exists_normal_index_two_of_not_fused_of_relIndex_eq_two {M Y : Subgroup G}
    (hY : Y.relIndex M = 2) (hM : ¬ 2 ∣ M.index) {x : G} (hxM : x ∈ M) (hxY : x ∉ Y) {a : ℕ}
    (hxo : orderOf x = 2 ^ a)
    (hmin : ∀ y ∈ M, y ∉ Y → IsPGroup 2 (zpowers y) → orderOf x ≤ orderOf y)
    (hfus : ∀ g : G, g⁻¹ * x * g ∉ Y) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hxT, hTM⟩ := CFSG.SeitzReduction.exists_sylow_mem_le_of_not_dvd_index hM hxM hxo
  have hUidx : ((T : Subgroup G) ⊓ Y).relIndex T = 2 := by
    rw [relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨x, hxT, fun h => hxY h.2, fun b hb => ?_⟩
    by_cases hbY : b ∈ Y
    · exact Or.inr ⟨hb, hbY⟩
    · refine Or.inl ⟨T.mul_mem hb hxT, ?_⟩
      have key := (mul_mem_iff_of_index_two (H := Y.subgroupOf M) hY
        (a := ⟨b, hTM hb⟩) (b := ⟨x, hxM⟩)).2 (by
          rw [mem_subgroupOf, mem_subgroupOf]
          exact iff_of_false hbY hxY)
      exact mem_subgroupOf.1 key
  exact CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson T.isPGroup' T.not_dvd_index
    inf_le_left hUidx hxT (fun h => hxY h.2)
    (fun y hyT hyU => hmin y (hTM hyT) (fun h => hyU ⟨hyT, h⟩)
      (T.isPGroup'.to_le (zpowers_le.2 hyT)))
    (fun g hg => hfus g hg.2)

theorem exists_normal_index_two_of_unique_of_relIndex_eq_two {M Y : Subgroup G} (hYM : Y ≤ M)
    (hY : Y.relIndex M = 2) {t : G} (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) {x : G}
    (hxM : x ∈ M) (hxY : x ∉ Y) {a : ℕ} (hxo : orderOf x = 2 ^ a)
    (hmin : ∀ y ∈ M, y ∉ Y → IsPGroup 2 (zpowers y) → orderOf x ≤ orderOf y) {n : ℕ}
    (hpow : IsConj t (x ^ n)) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := isConj_iff.1 hpow
  have hcM : c ∈ M := by
    have h1 : (c⁻¹)⁻¹ * t * c⁻¹ ∈ M := by
      rw [inv_inv, hc]
      exact M.pow_mem hxM n
    simpa using M.inv_mem (huniq c⁻¹ h1)
  have htM : t ∈ M := by
    have : t = c⁻¹ * x ^ n * c := by rw [← hc]; group
    rw [this]
    exact M.mul_mem (M.mul_mem (M.inv_mem hcM) (M.pow_mem hxM n)) hcM
  have hx2 : IsPGroup 2 (zpowers x) := IsPGroup.of_card (by rw [Nat.card_zpowers, hxo])
  have ht2 : IsPGroup 2 (zpowers t) := by
    obtain ⟨k, hk⟩ := (hx2.to_le (zpowers_le.2 (pow_mem (mem_zpowers x) n))).exists_card_eq
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, ← hc] at hk
    rw [Nat.card_zpowers, ← hk]
    simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj c) t).symm
  have hYn : (Y.subgroupOf M).Normal := normal_of_index_eq_two hY
  refine exists_normal_index_two_of_not_fused_of_relIndex_eq_two hY
    (not_dvd_index_of_unique htM ht2 huniq) hxM hxY hxo hmin (fun g hg => ?_)
  have hgM : g ∈ M := by
    have h1 : (c⁻¹ * g)⁻¹ * t * (c⁻¹ * g) ∈ M := by
      have : (c⁻¹ * g)⁻¹ * t * (c⁻¹ * g) = (g⁻¹ * x * g) ^ n := by
        have hcp := conj_pow (a := g⁻¹) (b := x) (i := n)
        rw [inv_inv] at hcp
        rw [hcp, ← hc]
        group
      rw [this]
      exact M.pow_mem (hYM hg) n
    simpa using M.mul_mem hcM (huniq _ h1)
  apply hxY
  have h2 := hYn.conj_mem ⟨g⁻¹ * x * g, hYM hg⟩ (mem_subgroupOf.2 hg) ⟨g, hgM⟩
  rw [mem_subgroupOf] at h2
  simpa [mul_assoc] using h2


end CFSG.SeitzReduction.F4Pilot
