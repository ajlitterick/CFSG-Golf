module

public import CFSG.GH74.Uniqueness.Bender.Unitary
public import CFSG.GH74.Uniqueness.Bender.Sylow2Basic

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup CFSG.BenderSuzuki

section Psl2

variable {K : Type*} [Group K] [Finite K]

theorem BenderType.sq_eq_one_of_two_pow_linear
    {J : Type*} [Group J] [Finite J] {n : ℕ}
    (hJ : BenderType J n 1 1) {x : J} {k : ℕ} (hx : x ^ 2 ^ k = 1) : x * x = 1 := by
  obtain ⟨S, -⟩ : ∃ S : Sylow 2 J, True := ⟨default, trivial⟩
  obtain ⟨t, hc⟩ := hJ.exists_benderCore S
  have hSZ : rootCenter (S : Subgroup J) = (S : Subgroup J) :=
    Subgroup.eq_of_le_of_card_ge (rootCenter_le _)
      (le_of_eq (by rw [hc.card_center, hc.card_eq, pow_one]))
  exact sq_eq_one_of_two_pow_of_sylow S
    (fun x hx => hc.center_sq x (by rw [hSZ]; exact hx)) hx

theorem BenderType.exists_psl2_pair_of_mem
    {n e : ℕ} (h : BenderType K n 3 e) {J : Subgroup K}
    (φ : J ≃* PSL2Model n) {z : K} (hzJ : z ∈ J) (hz : z * z = 1) :
    ∃ (Q : Sylow 2 K) (t : K), z ∈ rootCenter (Q : Subgroup K) ∧ t * t = 1 ∧ t ∈ J ∧
      t ∉ borel (Q : Subgroup K) ∧ rootCenter (Q : Subgroup K) ≤ J ∧
      rootCenter (Q : Subgroup K) ⊔ zpowers t = J := by
  classical
  have hn2 : 2 ≤ n := h.two_le.2
  have hJ : BenderType J n 1 1 := BenderType.linear n hn2 φ
  have : IsSimpleGroup J := hJ.isSimple
  obtain ⟨S, hzS⟩ := (isPGroup_two_zpowers_of_mul_self_eq_one (G := J) (z := ⟨z, hzJ⟩)
    (Subtype.ext hz)).exists_le_sylow
  obtain ⟨t₂, hc₂⟩ := hJ.exists_benderCore S
  have hSZ : rootCenter (S : Subgroup J) = (S : Subgroup J) :=
    Subgroup.eq_of_le_of_card_ge (rootCenter_le _)
      (le_of_eq (by rw [hc₂.card_center, hc₂.card_eq, pow_one]))
  obtain ⟨Z, hZdef⟩ : ∃ Z : Subgroup K, Z = (S : Subgroup J).map J.subtype := ⟨_, rfl⟩
  have hmemZ : ∀ x : J, (x : K) ∈ Z ↔ x ∈ (S : Subgroup J) := by
    intro x
    rw [hZdef]
    constructor
    · rintro ⟨s, hs, hsx⟩
      have : s = x := Subtype.ext hsx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hZsq : ∀ x ∈ Z, x * x = 1 := by
    intro x hx
    rw [hZdef] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    have := hc₂.center_sq s (by rw [hSZ]; exact hs)
    exact congrArg Subtype.val this
  have hZcard : Nat.card Z = 2 ^ n := by
    rw [hZdef, Subgroup.card_map_of_injective J.subtype_injective, hc₂.card_eq, pow_one]
  obtain ⟨Q, hZQ⟩ := (isPGroup_two_of_mul_self_eq_one hZsq).exists_le_sylow
  obtain ⟨t₀, hc₀⟩ := h.exists_benderCore Q
  have hZle : Z ≤ rootCenter (Q : Subgroup K) := hc₀.elemAbelian_le_rootCenter hZQ hZsq
  have hZeq : Z = rootCenter (Q : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge hZle (by rw [hZcard, hc₀.card_center])
  have ht₂sq : (t₂ : K) * t₂ = 1 := congrArg Subtype.val hc₂.sq_eq_one
  have ht₂Q : (t₂ : K) ∉ borel (Q : Subgroup K) := by
    intro hmem
    apply hc₂.not_mem
    rw [mem_borel_iff]
    intro x
    have h1 := mem_rootCenter_conj_iff hmem (x : K)
    rw [← hZeq] at h1
    exact (hmemZ x).symm.trans (h1.trans (hmemZ (t₂ * x * t₂⁻¹)))
  have hsup := hc₂.sup_zpowers_eq_top hc₂.not_mem
  have hJeq : Z ⊔ zpowers (t₂ : K) = J := by
    have h1 := congrArg (Subgroup.map J.subtype) hsup
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      ← hZdef] at h1
    exact h1
  have hzZ : z ∈ rootCenter (Q : Subgroup K) :=
    hZeq ▸ (hmemZ ⟨z, hzJ⟩).mpr (hzS (Subgroup.mem_zpowers _))
  refine ⟨Q, t₂, hzZ, ht₂sq, t₂.2, ht₂Q, ?_, ?_⟩
  · rw [← hZeq, hZdef]
    exact Subgroup.map_subtype_le _
  · rw [← hZeq]
    exact hJeq


end Psl2

end CFSG.GH74.Uniqueness.Bender
