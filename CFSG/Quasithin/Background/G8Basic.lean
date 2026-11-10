module

public import CFSG.LocalAnalysis.ComponentClassification.CoprimeAutomorphisms
public import CFSG.Quasithin.Background.A1cRank
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

open scoped Pointwise

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

structure G81 (X P A : Subgroup G) : Prop where
  elemAbelian : IsElemAbelian 2 A
  le_pGroup : A ≤ P
  pGroup : IsPGroup 2 P
  le_normalizer : P ≤ Subgroup.normalizer (X : Set G)
  nilpotent : Group.IsNilpotent X
  odd : Odd (Nat.card X)
  ne_bot : X ≠ ⊥

namespace G8

theorem eq_one_of_mem_of_odd {R X : Subgroup G} (hR : IsPGroup 2 R) (hX : Odd (Nat.card X))
    {x : G} (hxR : x ∈ R) (hxX : x ∈ X) : x = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hR ⟨x, hxR⟩
  have h1 : orderOf x = 2 ^ k := by rw [← Subgroup.orderOf_mk x hxR]; exact hk
  have h2 : orderOf x ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hxX
  have hcop : Nat.Coprime (2 ^ k) (Nat.card X) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hX)
  have h3 : orderOf x ∣ 1 := by
    have h4 : orderOf x ∣ 2 ^ k := by rw [h1]
    have := Nat.dvd_gcd h4 h2
    rwa [hcop.gcd_eq_one] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem eq_one_of_pow_two_pow_eq_one {X : Subgroup G} (hX : Odd (Nat.card X)) {x : G}
    (hx : x ∈ X) {m : ℕ} (h : x ^ 2 ^ m = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf x ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hx
  have hcop : Nat.Coprime (2 ^ m) (Nat.card X) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hX)
  have h3 := Nat.dvd_gcd h1 h2
  rw [hcop.gcd_eq_one] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem mem_normalizer_of_conj_mem {H : Subgroup G} {g : G} (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  simpa [mul_assoc] using this

theorem centralizer_sup (U N : Subgroup G) :
    Subgroup.centralizer ((U ⊔ N : Subgroup G) : Set G) =
      Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer (N : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (by exact_mod_cast le_sup_left))
      (Subgroup.centralizer_le (by exact_mod_cast le_sup_right))
  · intro x hx
    have hU : U ≤ Subgroup.centralizer {x} := fun u hu =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hx.1 u hu)
    have hN : N ≤ Subgroup.centralizer {x} := fun u hu =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hx.2 u hu)
    intro y hy
    have := sup_le hU hN hy
    exact Subgroup.mem_centralizer_singleton_iff.mp this

section Finite

variable [Finite G]

theorem centralizes_of_self_centralizing {X U R : Subgroup G} (hXn : Group.IsNilpotent X)
    (hXodd : Odd (Nat.card X)) (hUX : U ≤ X)
    (hself : X ⊓ Subgroup.centralizer (U : Set G) ≤ U) (hR : IsPGroup 2 R)
    (hRX : R ≤ Subgroup.normalizer (X : Set G)) (hRU : R ≤ Subgroup.centralizer (U : Set G)) :
    R ≤ Subgroup.centralizer (X : Set G) := by
  intro r hr
  have hK : Subgroup.zpowers r ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.zpowers_le.mpr (hRX hr)
  set α : MulAut X := conjAut hK ⟨r, Subgroup.mem_zpowers r⟩ with hα
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hR ⟨r, hr⟩
  have hord : orderOf r = 2 ^ k := by rw [← Subgroup.orderOf_mk r hr]; exact hk
  have hpow : α ^ orderOf r = 1 := by
    have : (⟨r, Subgroup.mem_zpowers r⟩ : Subgroup.zpowers r) ^ orderOf r = 1 := by
      apply Subtype.ext
      simp [pow_orderOf_eq_one]
    rw [hα, ← map_pow, this, map_one]
  have hcop : (orderOf r).Coprime (Nat.card X) := by
    rw [hord]; exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hXodd)
  have hself' : Subgroup.centralizer ((U.subgroupOf X : Subgroup X) : Set X) ≤ U.subgroupOf X := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    apply hself
    refine ⟨x.2, ?_⟩
    show (x : G) ∈ Subgroup.centralizer (U : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have := Subgroup.mem_centralizer_iff.mp hx ⟨u, hUX hu⟩ (Subgroup.mem_subgroupOf.mpr hu)
    exact congrArg Subtype.val this
  have hfix : ∀ u ∈ U.subgroupOf X, α u = u := by
    intro u hu
    apply Subtype.ext
    have hu' : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
    have hc := Subgroup.mem_centralizer_iff.mp (hRU hr) (u : G) hu'
    have hcoe : ((α u : X) : G) = r * (u : G) * r⁻¹ := by
      rw [hα]; exact conjAut_apply_coe hK ⟨r, Subgroup.mem_zpowers r⟩ u
    rw [hcoe, ← hc]
    simp
  have : Group.IsNilpotent X := hXn
  have h1 : α = 1 :=
    CFSG.ComponentClassification.CoprimeAutomorphisms.eq_one_of_self_centralizing_nilpotent
      (U.subgroupOf X) hself' α (orderOf r) hpow hcop hfix
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h2 := congrArg (fun β : MulAut X => ((β ⟨x, hx⟩ : X) : G)) h1
  have h3 : r * x * r⁻¹ = x := by
    have h4 : ((α ⟨x, hx⟩ : X) : G) = r * x * r⁻¹ := by
      rw [hα]; exact conjAut_apply_coe hK ⟨r, Subgroup.mem_zpowers r⟩ ⟨x, hx⟩
    rw [← h4]
    exact h2
  calc x * r = r * x * r⁻¹ * r := by rw [h3]
    _ = r * x := by group


theorem g8_4_of {X Q Y : Subgroup G} (hXn : Group.IsNilpotent X) (hXodd : Odd (Nat.card X))
    (hQ : IsPGroup 2 Q) (hQX : Q ≤ Subgroup.normalizer (X : Set G)) (hYX : Y ≤ X)
    (hQY : Q ≤ Subgroup.centralizer (Y : Set G))
    (hfaith : Q ⊓ Subgroup.centralizer (X : Set G) = ⊥) :
    Q ⊓ Subgroup.centralizer ((X ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G) = ⊥ := by
  set N := X ⊓ Subgroup.centralizer (Y : Set G) with hN
  set B := Q ⊓ Subgroup.centralizer (N : Set G) with hB
  have hBQ : B ≤ Q := inf_le_left
  have hUX : N ⊔ Y ≤ X := sup_le inf_le_left hYX
  have hself : X ⊓ Subgroup.centralizer ((N ⊔ Y : Subgroup G) : Set G) ≤ N ⊔ Y := by
    intro x hx
    rw [centralizer_sup] at hx
    exact le_sup_left (a := N) (b := Y) ⟨hx.1, hx.2.2⟩
  have hBc : B ≤ Subgroup.centralizer ((N ⊔ Y : Subgroup G) : Set G) := by
    rw [centralizer_sup]
    exact le_inf inf_le_right (hBQ.trans hQY)
  have := centralizes_of_self_centralizing hXn hXodd hUX hself (hQ.to_le hBQ)
    (hBQ.trans hQX) hBc
  rw [eq_bot_iff]
  intro x hx
  have hx1 : x ∈ Q ⊓ Subgroup.centralizer (X : Set G) := ⟨hx.1, this hx⟩
  rw [hfaith] at hx1
  exact hx1

end Finite

end G8

section Finite


end Finite

end CFSG.Quasithin
