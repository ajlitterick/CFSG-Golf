module

public import CFSG.Holt.PermFactsInvolutions
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Holt

open Equiv Equiv.Perm Finset

theorem closure_normal_of_conj_mem {G : Type*} [Group G] {s : Set G}
    (hs : ∀ g, ∀ x ∈ s, g * x * g⁻¹ ∈ s) : (Subgroup.closure s).Normal := by
  constructor
  intro n hn g
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (hs g x hx)
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

section Generation

variable {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ]

theorem exists_longInvolution (h : Odd (Nat.card Ψ)) (h3 : 3 ≤ Nat.card Ψ) :
    ∃ π : Perm Ψ, orderOf π = 2 ∧ ∃! x, π x = x := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨π, hπ⟩ := (exists_with_cycleType_iff (α := Ψ)
    (m := Multiset.replicate k 2)).2 ⟨by simp [← Nat.card_eq_fintype_card, hk]; omega,
      fun a ha => (Multiset.eq_of_mem_replicate ha).ge⟩
  have hsq : π ^ 2 = 1 := pow_prime_eq_one_iff.2 fun c hc => by
    rw [hπ] at hc
    exact Multiset.eq_of_mem_replicate hc
  have hne : π ≠ 1 := by
    rintro rfl
    rw [cycleType_one] at hπ
    have := congrArg Multiset.card hπ
    simp at this
    omega
  refine ⟨π, orderOf_eq_prime hsq hne, existsUnique_of_card_support_add_one ?_⟩
  rw [← sum_cycleType, hπ, hk]
  simp
  ring

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem closure_longInvolutions_perm_normal :
    (Subgroup.closure {π : Perm Ψ | orderOf π = 2 ∧ ∃! x, π x = x}).Normal := by
  refine closure_normal_of_conj_mem fun g π ⟨h2, h1⟩ => ⟨?_, ?_⟩
  · rw [← h2, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  · obtain ⟨a, ha, hu⟩ := h1
    refine ⟨g a, by simp [ha], fun y hy => ?_⟩
    have : π (g⁻¹ y) = g⁻¹ y := by
      simpa [Perm.mul_apply, eq_inv_iff_mul_eq_one, ← Perm.eq_inv_iff_eq] using hy
    rw [← hu _ this]
    simp

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem sq_eq_one_of_orderOf_eq_two {π : Perm Ψ} (h : orderOf π = 2) : π ^ 2 = 1 :=
  h ▸ pow_orderOf_eq_one π

theorem eq_top_of_alternatingGroup_le {H : Subgroup (Perm Ψ)} (hA : alternatingGroup Ψ ≤ H)
    {τ : Perm Ψ} (hτH : τ ∈ H) (hτ : sign τ = -1) : H = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  rcases Int.units_eq_one_or (sign σ) with hσ | hσ
  · exact hA hσ
  · rw [show σ = σ * τ⁻¹ * τ by group]
    exact mul_mem (hA (by simp [mem_alternatingGroup, hσ, hτ])) hτH

theorem closure_longInvolutions_eq_alternatingGroup (h : Nat.card Ψ % 4 = 1) :
    Subgroup.closure {π : Perm Ψ | orderOf π = 2 ∧ ∃! x, π x = x} = alternatingGroup Ψ := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro π ⟨hπ2, hπ1⟩
    exact (sign_eq_one_iff_of_existsUnique (sq_eq_one_of_orderOf_eq_two hπ2) hπ1).2 h
  · rcases (by omega : Nat.card Ψ = 1 ∨ 5 ≤ Nat.card Ψ) with h1 | h5
    · rw [alternatingGroup.eq_bot_of_card_le_two (by omega)]
      exact bot_le
    · have := closure_longInvolutions_perm_normal (Ψ := Ψ)
      obtain ⟨π, hπ⟩ := exists_longInvolution (Ψ := Ψ) (Nat.odd_iff.2 (by omega)) (by omega)
      refine Equiv.Perm.alternatingGroup_le_of_normal h5 ⟨⟨π, Subgroup.subset_closure hπ⟩, 1,
        fun h1 => ?_⟩
      have : π = 1 := congrArg Subtype.val h1
      rw [this, orderOf_one] at hπ
      exact absurd hπ.1 (by decide)

theorem closure_longInvolutions_eq_top (h : Nat.card Ψ % 4 = 3) :
    Subgroup.closure {π : Perm Ψ | orderOf π = 2 ∧ ∃! x, π x = x} = ⊤ := by
  rcases (by omega : Nat.card Ψ = 3 ∨ 7 ≤ Nat.card Ψ) with h3 | h7
  · rw [eq_top_iff, ← closure_isSwap]
    apply Subgroup.closure_mono
    rintro σ ⟨a, b, hab, rfl⟩
    refine ⟨orderOf_eq_prime (by rw [sq, swap_mul_self]) 
      (fun h1 => hab (by simpa using (congrArg (fun f : Perm Ψ => f a) h1).symm)),
      existsUnique_of_card_support_add_one ?_⟩
    rw [card_support_swap hab, h3]
  · have := closure_longInvolutions_perm_normal (Ψ := Ψ)
    obtain ⟨π, hπ⟩ := exists_longInvolution (Ψ := Ψ) (Nat.odd_iff.2 (by omega)) (by omega)
    have hπ1 : π ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hπ
      exact absurd hπ.1 (by decide)
    have hA : alternatingGroup Ψ ≤ Subgroup.closure {π : Perm Ψ | orderOf π = 2 ∧ ∃! x, π x = x} :=
      Equiv.Perm.alternatingGroup_le_of_normal (by omega) ⟨⟨π, Subgroup.subset_closure hπ⟩, 1,
        fun h1 => hπ1 (congrArg Subtype.val h1)⟩
    have hodd : sign π = -1 := by
      rcases Int.units_eq_one_or (sign π) with h1 | h1
      · have := (sign_eq_one_iff_of_existsUnique (sq_eq_one_of_orderOf_eq_two hπ.1) hπ.2).1 h1
        omega
      · exact h1
    exact eq_top_of_alternatingGroup_le hA (Subgroup.subset_closure hπ) hodd

theorem alternatingGroup_le_closure_longInvolutions (h : Odd (Nat.card Ψ)) :
    alternatingGroup Ψ ≤ Subgroup.closure {π : Perm Ψ | orderOf π = 2 ∧ ∃! x, π x = x} := by
  rcases (by rw [Nat.odd_iff] at h; omega : Nat.card Ψ % 4 = 1 ∨ Nat.card Ψ % 4 = 3) with h1 | h3
  · rw [closure_longInvolutions_eq_alternatingGroup h1]
  · rw [closure_longInvolutions_eq_top h3]
    exact le_top

end Generation

section Normal

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

theorem eq_one_of_forall_commute_alternatingGroup (h4 : 4 ≤ Nat.card Λ) {c : Perm Λ}
    (hc : ∀ a ∈ alternatingGroup Λ, Commute c a) : c = 1 := by
  ext x
  by_contra hx
  rw [Perm.one_apply] at hx
  have hcard : 1 < #(univ \ {x, c x}) := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, card_pair (Ne.symm hx),
      ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨y, hy, z, hz, hyz⟩ := one_lt_card.1 hcard
  simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and, not_or] at hy hz
  set σ := swap x y * swap x z
  have hσ : IsThreeCycle σ := isThreeCycle_swap_mul_swap_same (Ne.symm hy.1) (Ne.symm hz.1) hyz
  have h1 : σ x = z := by
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hz.1 (Ne.symm hyz)]
  have h2 : σ (c x) = c x := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hx (Ne.symm hz.2),
      swap_apply_of_ne_of_ne hx (Ne.symm hy.2)]
  have hcomm : c (σ x) = σ (c x) :=
    congrArg (fun f : Perm Λ => f x) (hc σ hσ.mem_alternatingGroup).eq
  rw [h1, h2] at hcomm
  exact hz.1 (c.injective hcomm)

theorem eq_bot_or_alternatingGroup_le (h5 : 5 ≤ Nat.card Λ) {N : Subgroup (Perm Λ)}
    (hN : alternatingGroup Λ ≤ Subgroup.normalizer (N : Set (Perm Λ))) :
    N = ⊥ ∨ alternatingGroup Λ ≤ N := by
  set A := alternatingGroup Λ
  have hM : ((N ⊓ A).subgroupOf A).Normal := by
    refine ⟨fun m hm a => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hm ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨(Subgroup.mem_normalizer_iff.1 (hN a.2) m).1 hm.1,
      mul_mem (mul_mem a.2 hm.2) (inv_mem a.2)⟩
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top h5 (N := (N ⊓ A).subgroupOf A)
    with h | h
  · left
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    refine eq_one_of_forall_commute_alternatingGroup (by omega) fun a ha => ?_
    have hk : n * a * n⁻¹ * a⁻¹ ∈ N ⊓ A := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [show n * a * n⁻¹ * a⁻¹ = n * (a * n⁻¹ * a⁻¹) by group]
        exact mul_mem hn ((Subgroup.mem_normalizer_iff.1 (hN ha) _).1 (inv_mem hn))
      · exact mul_mem ((alternatingGroup.normal).conj_mem a ha n) (inv_mem ha)
    have hk1 : (⟨_, hk.2⟩ : A) ∈ (N ⊓ A).subgroupOf A := by
      rw [Subgroup.mem_subgroupOf]
      exact hk
    rw [h, Subgroup.mem_bot] at hk1
    have := congrArg Subtype.val hk1
    simp only [OneMemClass.coe_one] at this
    rw [Commute, SemiconjBy, ← mul_inv_eq_one, mul_inv_rev, ← mul_assoc]
    exact this
  · right
    intro a ha
    have : (⟨a, ha⟩ : A) ∈ (N ⊓ A).subgroupOf A := by
      rw [h]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf] at this
    exact this.1

theorem eq_bot_or_eq_alternatingGroup_or_eq_top_of_normal (h5 : 5 ≤ Nat.card Λ)
    {N : Subgroup (Perm Λ)} [N.Normal] : N = ⊥ ∨ N = alternatingGroup Λ ∨ N = ⊤ := by
  rcases eq_bot_or_alternatingGroup_le h5 (N := N) (by
    rw [Subgroup.normalizer_eq_top N]
    exact le_top) with h | h
  · exact Or.inl h
  · right
    by_cases hN : ∃ τ ∈ N, sign τ = -1
    · obtain ⟨τ, hτN, hτ⟩ := hN
      exact Or.inr (eq_top_of_alternatingGroup_le h hτN hτ)
    · push Not at hN
      refine Or.inl (le_antisymm (fun τ hτ => ?_) h)
      rcases Int.units_eq_one_or (sign τ) with h1 | h1
      · exact h1
      · exact absurd h1 (hN τ hτ)


end Normal

section Semiregular


end Semiregular

section Product


end Product

section Subset


end Subset

section TransitiveExtension

open scoped Pointwise


end TransitiveExtension

end CFSG.Holt
