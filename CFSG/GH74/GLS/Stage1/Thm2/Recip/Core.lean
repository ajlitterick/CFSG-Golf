module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.GH74.GLS.Stage1.Thm6.Prelude

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_normalizer_closure_of_gen {T : Set G} {c : G}
    (h1 : ∀ g ∈ T, c⁻¹ * g * c ∈ closure T) (h2 : ∀ g ∈ T, c * g * c⁻¹ ∈ closure T) :
    c ∈ normalizer ((closure T : Subgroup G) : Set G) := by
  have a1 : ∀ t ∈ closure T, c⁻¹ * t * c ∈ closure T := by
    intro t ht
    have : closure T ≤ (closure T).comap (MulAut.conj c⁻¹).toMonoidHom := by
      rw [closure_le]
      intro g hg
      simpa [MulAut.conj_apply] using h1 g hg
    simpa [MulAut.conj_apply] using this ht
  have a2 : ∀ t ∈ closure T, c * t * c⁻¹ ∈ closure T := by
    intro t ht
    have : closure T ≤ (closure T).comap (MulAut.conj c).toMonoidHom := by
      rw [closure_le]
      intro g hg
      simpa [MulAut.conj_apply] using h2 g hg
    simpa [MulAut.conj_apply] using this ht
  rw [mem_normalizer_iff]
  intro t
  exact ⟨fun ht => a2 t ht, fun ht => by simpa [mul_assoc] using a1 _ ht⟩

theorem exists_invariant_sylow [Finite G] {H A : Subgroup G} (hA : IsPGroup 2 A)
    (hAH : A ≤ normalizer (H : Set G)) :
    ∃ S : Subgroup G, IsSylow2In S H ∧ A ≤ normalizer (S : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : A →* MulAut H := H.normalizerMonoidHom.comp (Subgroup.inclusion hAH)
  let _ : MulDistribMulAction A H := MulDistribMulAction.compHom H φ
  let _ : MulAction A (Sylow 2 H) := Sylow.pointwiseMulAction
  have hcard : ¬ 2 ∣ Nat.card (Sylow 2 H) := by
    intro h
    have h1 := card_sylow_modEq_one 2 H
    have h2 : Nat.card (Sylow 2 H) % 2 = 0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.ModEq, h2, Nat.mod_eq_of_lt (Fact.out : Nat.Prime 2).one_lt] at h1
    exact zero_ne_one h1
  obtain ⟨Q₀, hQ₀⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 H) hcard
  refine ⟨(Q₀ : Subgroup H).map H.subtype, ⟨map_subtype_le _, Q₀.isPGroup'.map _, ?_⟩, ?_⟩
  · have e : ((Q₀ : Subgroup H).map H.subtype).subgroupOf H = (Q₀ : Subgroup H) :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [Subgroup.relIndex, e]
    exact Q₀.not_dvd_index
  · rw [le_normalizer_iff]
    rintro b hb _ ⟨y, hy, rfl⟩
    have hfix : (⟨b, hb⟩ : A) • Q₀ = Q₀ := (MulAction.mem_fixedPoints.mp hQ₀) ⟨b, hb⟩
    have hmem : (⟨b, hb⟩ : A) • y ∈ (Q₀ : Subgroup H) := by
      have h := Subgroup.smul_mem_pointwise_smul y (⟨b, hb⟩ : A) (Q₀ : Subgroup H) hy
      rwa [← Sylow.pointwise_smul_def, hfix] at h
    refine ⟨_, hmem, ?_⟩
    change (((H.normalizerMonoidHom) (Subgroup.inclusion hAH ⟨b, hb⟩)) y : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl

theorem eq_one_or_eq_of_mem_zpowers {x y : G} (hx : x * x = 1) (hy : y ∈ zpowers x) :
    y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  have hsq : x ^ 2 = 1 := by rw [pow_two]; exact hx
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hx]
    simp
  · right
    rw [zpow_add, zpow_mul, zpow_one, zpow_two, hx]
    simp

theorem isPGroup_zpowers_of_mul_self_eq_one {s : G} (hs : s * s = 1) : IsPGroup 2 ↥(zpowers s) := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rcases eq_one_or_eq_of_mem_zpowers hs g.2 with h | h <;> rw [Subgroup.coe_pow, h] <;>
    simp [pow_two, hs]

theorem isPGroup_zpowers_of_pow_eq_one [Finite G] {a : G} {n : ℕ} (h : a ^ (2 ^ n) = 1) :
    IsPGroup 2 ↥(zpowers a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])


theorem mem_closure_pair {s x t : G} (hs : s * s = 1) (hx : x * x = 1) (hsx : s * x = x * s)
    (ht : t ∈ closure ({s, x} : Set G)) : t = 1 ∨ t = s ∨ t = x ∨ t = s * x := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have h_sp : s * (s * x) = x := by rw [← mul_assoc, hs, one_mul]
  have h_xs : x * s = s * x := hsx.symm
  have h_xp : x * (s * x) = s := by rw [← mul_assoc, ← hsx, mul_assoc, hx, mul_one]
  have h_ps : s * x * s = x := by rw [mul_assoc, ← hsx, ← mul_assoc, hs, one_mul]
  have h_px : s * x * x = s := by rw [mul_assoc, hx, mul_one]
  have h_pp : s * x * (s * x) = 1 := by rw [← mul_assoc, h_ps, hx]
  induction ht using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with hz | hz
    · rw [hz]; exact Or.inr (Or.inl rfl)
    · rw [hz]; exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul a b _ _ ha hb =>
    rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> rw [ha, hb] <;>
      simp [hs, hx, h_sp, h_xs, h_xp, h_ps, h_px, h_pp]
  | inv a _ ha =>
    rcases ha with ha | ha | ha | ha <;> rw [ha]
    · simp
    · rw [hsinv]; simp
    · rw [hxinv]; simp
    · rw [mul_inv_rev, hsinv, hxinv, h_xs]; simp


theorem fusion_of_inverted {s x a : G} (hs : s * s = 1) (hx : x * x = 1) (hsx : s * x = x * s)
    (hax : a * x = x * a) (ha2 : a * a = x) (hinv : s * a * s⁻¹ = a⁻¹) :
    a ∈ normalizer ((closure ({s, x} : Set G) : Subgroup G) : Set G) ∧ a⁻¹ * s * a = s * x := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hsa : s * a = a⁻¹ * s := by
    calc s * a = s * a * s⁻¹ * s := by group
      _ = a⁻¹ * s := by rw [hinv]
  have hainv : a⁻¹ = a * x := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, ha2, hx]
  have haa : a⁻¹ * a⁻¹ = x := by rw [← mul_inv_rev, ha2, hxinv]
  have h1 : a⁻¹ * s * a = s * x := by
    calc a⁻¹ * s * a = a⁻¹ * (s * a) := by group
      _ = a⁻¹ * (a⁻¹ * s) := by rw [hsa]
      _ = (a⁻¹ * a⁻¹) * s := by group
      _ = x * s := by rw [haa]
      _ = s * x := hsx.symm
  have h2 : a * s * a⁻¹ = s * x := by
    calc a * s * a⁻¹ = a * s * (a * x) := by rw [hainv]
      _ = a * (s * a) * x := by group
      _ = a * (a⁻¹ * s) * x := by rw [hsa]
      _ = s * x := by group
  have hx1 : a⁻¹ * x * a = x := by
    calc a⁻¹ * x * a = a⁻¹ * (x * a) := by group
      _ = a⁻¹ * (a * x) := by rw [hax]
      _ = x := by group
  have hx2 : a * x * a⁻¹ = x := by
    calc a * x * a⁻¹ = (a * x) * a⁻¹ := rfl
      _ = (x * a) * a⁻¹ := by rw [hax]
      _ = x := by group
  have hsxm : s * x ∈ closure ({s, x} : Set G) :=
    mul_mem (subset_closure (Or.inl rfl)) (subset_closure (Or.inr rfl))
  refine ⟨mem_normalizer_closure_of_gen (fun g hg => ?_) (fun g hg => ?_), h1⟩
  · rcases hg with rfl | rfl
    · rw [h1]; exact hsxm
    · rw [hx1]; exact subset_closure (Or.inr rfl)
  · rcases hg with rfl | rfl
    · rw [h2]; exact hsxm
    · rw [hx2]; exact subset_closure (Or.inr rfl)

theorem swap_of_two_fusions {s x g₁ g₂ : G} (hx : x * x = 1) (hsx : s * x = x * s)
    (h1x : g₁⁻¹ * x * g₁ = x) (h1s : g₁⁻¹ * s * g₁ = s * x)
    (h2s : g₂⁻¹ * s * g₂ = s) (h2x : g₂⁻¹ * x * g₂ = x * s) (hs : s * s = 1) :
    ∃ g : G, g⁻¹ * x * g = s ∧ g⁻¹ * s * g = x := by
  have h3 : s * (x * s) = x := by rw [← hsx, ← mul_assoc, hs, one_mul]
  refine ⟨g₁ * g₂ * g₁, ?_, ?_⟩
  · calc (g₁ * g₂ * g₁)⁻¹ * x * (g₁ * g₂ * g₁)
        = g₁⁻¹ * (g₂⁻¹ * (g₁⁻¹ * x * g₁) * g₂) * g₁ := by group
      _ = g₁⁻¹ * (g₂⁻¹ * x * g₂) * g₁ := by rw [h1x]
      _ = g₁⁻¹ * (x * s) * g₁ := by rw [h2x]
      _ = (g₁⁻¹ * x * g₁) * (g₁⁻¹ * s * g₁) := by group
      _ = x * (s * x) := by rw [h1x, h1s]
      _ = s := by rw [← mul_assoc, ← hsx, mul_assoc, hx, mul_one]
  · calc (g₁ * g₂ * g₁)⁻¹ * s * (g₁ * g₂ * g₁)
        = g₁⁻¹ * (g₂⁻¹ * (g₁⁻¹ * s * g₁) * g₂) * g₁ := by group
      _ = g₁⁻¹ * (g₂⁻¹ * (s * x) * g₂) * g₁ := by rw [h1s]
      _ = g₁⁻¹ * ((g₂⁻¹ * s * g₂) * (g₂⁻¹ * x * g₂)) * g₁ := by group
      _ = g₁⁻¹ * (s * (x * s)) * g₁ := by rw [h2s, h2x]
      _ = g₁⁻¹ * x * g₁ := by rw [h3]
      _ = x := h1x

end CFSG.GH74.GLS.Stage1.Thm2.Recip
