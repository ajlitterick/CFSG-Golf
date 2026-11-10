module

public import CFSG.LocalAnalysis.StandardType.GGSix
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Group

variable {G : Type*} [Group G]

theorem mem_normalizer_centralizer {S : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (S : Set G)) :
    x ∈ Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  have key : ∀ y ∈ Subgroup.normalizer (S : Set G), ∀ c ∈ Subgroup.centralizer (S : Set G),
      y * c * y⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro y hy c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have hs' : y⁻¹ * s * y ∈ S := (Subgroup.mem_normalizer_iff''.mp hy s).mp hs
    have := hc _ hs'
    calc s * (y * c * y⁻¹) = y * ((y⁻¹ * s * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * s * y)) * y⁻¹ := by rw [this]
      _ = y * c * y⁻¹ * s := by group
  refine Subgroup.mem_normalizer_iff.mpr fun c => ⟨key x hx c, fun hc => ?_⟩
  have := key x⁻¹ (Subgroup.inv_mem _ hx) _ hc
  simpa [mul_assoc] using this

theorem not_dvd_card_of_isCyclic_of_mem_normalizer [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {N Y : Subgroup G} {x : G} (hx : orderOf x = p) (hxN : x ∉ N)
    (hxn : x ∈ Subgroup.normalizer (N : Set G)) (hNY : N ≤ Y) (hxY : x ∈ Y)
    (hcyc : ∀ S : Subgroup G, S ≤ Y → IsPGroup p S → IsCyclic S) : ¬ p ∣ Nat.card N := by
  set n : Subgroup.normalizer (N : Set G) := ⟨x, hxn⟩ with hn
  have hno : orderOf n = p := by rw [hn, Subgroup.orderOf_mk]; exact hx
  have hPp : IsPGroup p (Subgroup.zpowers n) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hno, pow_one])
  have hcard : ¬ p ∣ Nat.card (Sylow p N) := by
    intro h
    have h1 := (Nat.modEq_zero_iff_dvd.mpr h).symm.trans (card_sylow_modEq_one p N)
    have h2 : p ∣ 1 := (Nat.modEq_iff_dvd' (Nat.zero_le 1)).mp h1
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp h2)
  obtain ⟨S, hS⟩ := hPp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p N) hcard
  have hfix : ∀ k : ℤ, n ^ k • S = S := fun k =>
    hS ⟨n ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩⟩
  set S' : Subgroup G := (S : Subgroup N).map N.subtype with hS'
  have hconj : ∀ k : ℤ, ∀ a ∈ S', x ^ k * a * (x ^ k)⁻¹ ∈ S' := by
    intro k a ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    have hmem : n ^ k • b ∈ ((n ^ k • S : Sylow p N) : Subgroup N) := by
      rw [Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul b (n ^ k) (S : Subgroup N) hb
    rw [hfix k] at hmem
    refine Subgroup.mem_map.mpr ⟨_, hmem, ?_⟩
    have hk : ((n ^ k : Subgroup.normalizer (N : Set G)) : G) = x ^ k := by simp [hn]
    change ((n ^ k : Subgroup.normalizer (N : Set G)) : G) * (b : G) *
      ((n ^ k : Subgroup.normalizer (N : Set G)) : G)⁻¹ = x ^ k * (b : G) * (x ^ k)⁻¹
    rw [hk]
  have hxS' : x ∈ Subgroup.normalizer (S' : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun a => ⟨fun ha => by simpa using hconj 1 a ha,
      fun ha => ?_⟩
    have := hconj (-1) _ ha
    simpa [mul_assoc] using this
  have hS'p : IsPGroup p S' := S.isPGroup'.map N.subtype
  have hxp : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hCp : IsPGroup p (S' ⊔ Subgroup.zpowers x : Subgroup G) :=
    hS'p.to_sup_of_normal_left' hxp (Subgroup.zpowers_le.mpr hxS')
  have hS'N : S' ≤ N := Subgroup.map_subtype_le _
  have hCY : S' ⊔ Subgroup.zpowers x ≤ Y := sup_le (hS'N.trans hNY) (Subgroup.zpowers_le.mpr hxY)
  have hCcyc : IsCyclic (S' ⊔ Subgroup.zpowers x : Subgroup G) := hcyc _ hCY hCp
  have hS'dvd : ¬ p ∣ Nat.card S' := by
    intro hdvd
    have hr : Subgroup.zpowers x ≤ S' ⊔ Subgroup.zpowers x := le_sup_right
    have hl : S' ≤ S' ⊔ Subgroup.zpowers x := le_sup_left
    have hle : (Subgroup.zpowers x).subgroupOf (S' ⊔ Subgroup.zpowers x) ≤
        S'.subgroupOf (S' ⊔ Subgroup.zpowers x) := by
      rw [IsCyclic.subgroup_le_iff_card_dvd,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hr).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hl).toEquiv, Nat.card_zpowers, hx]
      exact hdvd
    have : (⟨x, hr (Subgroup.mem_zpowers x)⟩ : ↥(S' ⊔ Subgroup.zpowers x)) ∈
        S'.subgroupOf (S' ⊔ Subgroup.zpowers x) :=
      hle (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers x))
    exact hxN (hS'N (Subgroup.mem_subgroupOf.mp this))
  have hScard : Nat.card (S : Subgroup N) = 1 := by
    rcases S.isPGroup'.card_eq_or_dvd with h | h
    · exact h
    · exact absurd (by rwa [hS', Subgroup.card_map_of_injective Subtype.coe_injective]) hS'dvd
  rw [← Subgroup.card_mul_index (S : Subgroup N), hScard, one_mul]
  exact S.not_dvd_index

theorem mem_normalizer_pCoreOf {p : ℕ} {H : Subgroup G} {n : G} (hn : n ∈ H) :
    n ∈ Subgroup.normalizer (pCoreOf p H : Set G) := by
  have key : ∀ m ∈ H, ∀ h ∈ pCoreOf p H, m * h * m⁻¹ ∈ pCoreOf p H := by
    intro m hm h hh
    obtain ⟨h', hh', rfl⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨⟨m, hm⟩ * h' * ⟨m, hm⟩⁻¹, ?_, rfl⟩
    exact (Dichotomy.CentralizerContainment.pCore_normal_assembly p H).conj_mem h' hh' _
  refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨key n hn h, fun hh => ?_⟩
  have := key n⁻¹ (H.inv_mem hn) _ hh
  simpa [mul_assoc] using this

end Group

section Ctx


end Ctx

end CFSG.StandardType
