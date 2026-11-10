module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndFieldBasic

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.SeitzReduction.F4Pilot

variable {G : Type*} [Group G]

section Outer

variable {X : Type*} [Group X] {G₀ : Subgroup G}

theorem not_mem_of_normalizerMulAut_not_mem_range (e : G₀ ≃* X) {t : G}
    (htN : t ∈ normalizer (G₀ : Set G))
    (hout : normalizerMulAut e ⟨t, htN⟩ ∉ (MulAut.conj : X →* MulAut X).range) : t ∉ G₀ :=
  fun htG => hout ⟨e ⟨t, htG⟩, (normalizerMulAut_of_mem e htG).symm⟩

theorem ne_bot_of_normalizerMulAut_not_mem_range (e : G₀ ≃* X) {t : G}
    (htN : t ∈ normalizer (G₀ : Set G))
    (hout : normalizerMulAut e ⟨t, htN⟩ ∉ (MulAut.conj : X →* MulAut X).range) : G₀ ≠ ⊥ := by
  intro hbot
  have hX : ∀ x : X, x = 1 := fun x => by
    have h1 : ((e.symm x : G₀) : G) = 1 :=
      (Subgroup.eq_bot_iff_forall G₀).1 hbot _ (e.symm x).2
    rw [← e.apply_symm_apply x, show e.symm x = 1 from Subtype.ext h1, map_one]
  exact hout ⟨1, MulEquiv.ext fun x => (hX _).trans (hX _).symm⟩

theorem two_lt_card_of_normalizerMulAut_not_mem_range [Finite G] (e : G₀ ≃* X) {t : G}
    (htN : t ∈ normalizer (G₀ : Set G))
    (hout : normalizerMulAut e ⟨t, htN⟩ ∉ (MulAut.conj : X →* MulAut X).range) :
    2 < Nat.card G := by
  have h1 : 1 < Nat.card G₀ :=
    (Subgroup.one_lt_card_iff_ne_bot _).2 (ne_bot_of_normalizerMulAut_not_mem_range e htN hout)
  have h2 : 1 < G₀.index := Subgroup.one_lt_index_of_ne_top fun h =>
    not_mem_of_normalizerMulAut_not_mem_range e htN hout (h ▸ mem_top t)
  rw [← G₀.card_mul_index]
  nlinarith

end Outer

variable [Finite G]

theorem exists_normal_index_two_of_unique_of_not_four_dvd {M : Subgroup G} {t : G} (htM : t ∈ M)
    (ht : orderOf t = 2) (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M)
    {Q : Type*} [Group Q] [Finite Q] (ψ : M →* Q) (hQ : ¬ 4 ∣ Nat.card Q)
    (hψt : ψ ⟨t, htM⟩ ≠ 1) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  set z : ψ.range := ψ.rangeRestrict ⟨t, htM⟩ with hz
  have hzo : orderOf z = 2 ^ 1 := by
    have h1 : orderOf z ∣ 2 := by
      refine (orderOf_map_dvd _ _).trans ?_
      rw [Subgroup.orderOf_mk, ht]
    have h2 : z ≠ 1 := fun h => hψt (congrArg Subtype.val h)
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) h2
    · rw [h, pow_one]
  have hQ' : ¬ 2 ^ (1 + 1) ∣ Nat.card ψ.range := fun h =>
    hQ (h.trans (Subgroup.card_subgroup_dvd_card _))
  obtain ⟨R, hRidx, hzR, -⟩ := exists_index_two_of_orderOf_eq_two_pow le_rfl hzo hQ'
  set Y := (R.comap ψ.rangeRestrict).map M.subtype with hY
  have hYM : Y ≤ M := map_subtype_le _
  have hYidx : Y.relIndex M = 2 := by
    rw [relIndex, hY, ← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective,
      index_comap_of_surjective _ ψ.rangeRestrict_surjective, hRidx]
  have htY : t ∉ Y := by
    rintro ⟨m, hm, hmt⟩
    have hm' : m = ⟨t, htM⟩ := Subtype.ext hmt
    subst hm'
    exact hzR hm
  refine exists_normal_index_two_of_unique_of_relIndex_eq_two hYM hYidx huniq htM htY
    (a := 1) (by rw [ht, pow_one]) (fun y _ hyY _ => ?_) (n := 1)
    (isConj_iff.2 ⟨1, by simp⟩)
  have hy1 : y ≠ 1 := fun h => hyY (h ▸ Y.one_mem)
  have hy2 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
  have := orderOf_pos y
  omega

theorem exists_normal_index_two_of_mulAut_hom {X : Type*} [Group X] {G₀ : Subgroup G}
    (e : G₀ ≃* X) {t : G} (htN : t ∈ normalizer (G₀ : Set G)) (ht : orderOf t = 2)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G))
    {Q : Type*} [Group Q] [Finite Q] (χ : MulAut X →* Q) (hQ : ¬ 4 ∣ Nat.card Q)
    (hχt : χ (normalizerMulAut e ⟨t, htN⟩) ≠ 1) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 :=
  exists_normal_index_two_of_unique_of_not_four_dvd htN ht huniq (χ.comp (normalizerMulAut e)) hQ
    hχt

theorem false_of_simple_of_mulAut_hom [IsSimpleGroup G] {X : Type*} [Group X] {G₀ : Subgroup G}
    (e : G₀ ≃* X) {t : G} (htN : t ∈ normalizer (G₀ : Set G)) (ht : orderOf t = 2)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G))
    {Q : Type*} [Group Q] [Finite Q] (χ : MulAut X →* Q) (hQ : ¬ 4 ∣ Nat.card Q)
    (hχInn : ∀ x : X, χ (MulAut.conj x) = 1) (hχt : χ (normalizerMulAut e ⟨t, htN⟩) ≠ 1) :
    False := by
  have hout : normalizerMulAut e ⟨t, htN⟩ ∉ (MulAut.conj : X →* MulAut X).range := by
    rintro ⟨x, hx⟩
    exact hχt (hx ▸ hχInn x)
  exact CFSG.SeitzReduction.not_exists_normal_index_two_of_simple
    (two_lt_card_of_normalizerMulAut_not_mem_range e htN hout)
    (exists_normal_index_two_of_mulAut_hom e htN ht huniq χ hQ hχt)

section Complement

variable {X : Type*} [Group X] {G₀ : Subgroup G} (hC : centralizer (G₀ : Set G) = ⊥)
  (e : G₀ ≃* X) {C : Subgroup (MulAut X)} [IsCyclic C]
  (hCInn : ∀ β ∈ C, β ∈ (MulAut.conj : X →* MulAut X).range → β = 1)
  (hNF : ∀ α : MulAut X, ∃ g : X, ∃ β ∈ C, α = MulAut.conj g * β)


theorem eq_of_sq_eq_one_of_ne_one_of_isCyclic {C' : Type*} [Group C'] [Finite C'] [IsCyclic C']
    {u z : C'} (hu : u ^ 2 = 1) (hz : z ^ 2 = 1) (hu1 : u ≠ 1) (hz1 : z ≠ 1) : u = z := by
  classical
  have := Fintype.ofFinite C'
  by_contra h
  have hsub : ({1, z, u} : Finset C') ⊆ Finset.univ.filter (fun a : C' => a ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter]
    rcases hx with rfl | rfl | rfl
    · exact ⟨Finset.mem_univ _, one_pow 2⟩
    · exact ⟨Finset.mem_univ _, hz⟩
    · exact ⟨Finset.mem_univ _, hu⟩
  have h3 : ({1, z, u} : Finset C').card = 3 :=
    Finset.card_eq_three.2 ⟨1, z, u, hz1.symm, hu1.symm, fun e => h e.symm, rfl⟩
  have hle := IsCyclic.card_pow_eq_one_le (α := C') (n := 2) (by norm_num)
  have := Finset.card_le_card hsub
  omega


end Complement

end CFSG.SeitzReduction.EPilot
