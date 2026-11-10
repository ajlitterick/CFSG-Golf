module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Moving

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section General

variable {G : Type} [Group G]

theorem inv_mul_conj_pow_mem_of_normalizer {V : Subgroup G} {g z : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (h : z⁻¹ * (g⁻¹ * z * g) ∈ V) :
    ∀ k : ℕ, z⁻¹ * ((g ^ k)⁻¹ * z * g ^ k) ∈ V := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : g⁻¹ * (z⁻¹ * ((g ^ k)⁻¹ * z * g ^ k)) * g ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) _).mp ih
      simpa using this
    have e : z⁻¹ * ((g ^ (k + 1))⁻¹ * z * g ^ (k + 1)) =
        (z⁻¹ * (g⁻¹ * z * g)) * (g⁻¹ * (z⁻¹ * ((g ^ k)⁻¹ * z * g ^ k)) * g) := by
      rw [pow_succ]
      group
    rw [e]
    exact V.mul_mem h h2

theorem not_independent_of_mem_zpowers [Finite G] {p : ℕ} [Fact p.Prime] {e c₁ c₂ : G}
    (hep : e ^ p = 1)
    (hc₁ : c₁ ∈ Subgroup.zpowers e) (hc₂ : c₂ ∈ Subgroup.zpowers e) (V : Subgroup G)
    (hind : ∀ i j : ℕ, c₁ ^ i * c₂ ^ j ∈ V → p ∣ i ∧ p ∣ j) : False := by
  have hp := (Fact.out : p.Prime)
  have hV1 : (1 : G) ∈ V := one_mem _
  have hc₁p : c₁ ^ p = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc₁
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hep, one_zpow]
  by_cases h1 : c₁ = 1
  · have := hind 1 0 (by rw [h1, one_pow, pow_zero, one_mul]; exact hV1)
    exact hp.one_lt.ne' (Nat.dvd_one.mp this.1)
  · have heq := zpowers_eq_of_mem_of_ne_one hep hc₁ h1
    have hc₂' : c₂ ∈ Subgroup.zpowers c₁ := heq ▸ hc₂
    obtain ⟨m, hm⟩ := (mem_powers_iff_mem_zpowers.mpr hc₂' : c₂ ∈ Submonoid.powers c₁)
    have := hind (m * (p - 1)) 1 (by
      rw [pow_one, ← hm, ← pow_add, ← mul_add_one, Nat.sub_add_cancel hp.one_lt.le, mul_comm,
        pow_mul, hc₁p, one_pow]
      exact hV1)
    exact hp.one_lt.ne' (Nat.dvd_one.mp this.2)

end General

section Moving

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem GGL45Config.comm_mem_V_of_torus (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    {s : ℕ} (hs : 2 ≤ s) {x' : G} (hx'x : Subgroup.zpowers x' = Subgroup.zpowers x)
    (hx'V : ∀ u ∈ U₁, (u ^ (1 + p ^ (s - 1)))⁻¹ * (x'⁻¹ * u * x') ∈
      U ⊓ Subgroup.centralizer (K : Set G))
    {z : G} (hz : z ∈ U₁) (hzp : z ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G)) :
    x * z * x⁻¹ * z⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G) := by
  set V : Subgroup G := U ⊓ Subgroup.centralizer (K : Set G) with hV
  have hzU : z ∈ U := hcfg.part_le hz
  have hxU : x ∈ U := hcfg.bs_le hcfg.x_mem
  have hNV : ∀ u ∈ U, u ∈ Subgroup.normalizer (V : Set G) := fun u hu =>
    mem_normalizer_of_forall_conj_mem fun v hv => by
      have := hcfg.conj_mem_V (U.inv_mem hu) hv
      rwa [inv_inv] at this
  have hx'U : x' ∈ U :=
    (Subgroup.zpowers_le.mpr hxU) (hx'x ▸ Subgroup.mem_zpowers x')
  have hzN : z ^ p ^ (s - 1) ∈ V := by
    have e : p ^ (s - 1) = p * p ^ (s - 2) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [e, pow_mul]
    exact V.pow_mem hzp _
  have h1 : z⁻¹ * (x'⁻¹ * z * x') ∈ V := by
    have h := hx'V z hz
    have e : z⁻¹ * (x'⁻¹ * z * x') =
        z ^ p ^ (s - 1) * ((z ^ (1 + p ^ (s - 1)))⁻¹ * (x'⁻¹ * z * x')) := by
      rw [pow_add, pow_one]
      group
    rw [e]
    exact V.mul_mem hzN h
  obtain ⟨k, hk⟩ : ∃ k : ℕ, x' ^ k = x⁻¹ := (Submonoid.mem_powers_iff _ _).mp
    (mem_powers_iff_mem_zpowers.mpr (hx'x ▸ inv_mem (Subgroup.mem_zpowers x) :
      x⁻¹ ∈ Subgroup.zpowers x'))
  have h2 := inv_mul_conj_pow_mem_of_normalizer (hNV x' hx'U) h1 k
  rw [hk, inv_inv] at h2
  have h3 := (Subgroup.mem_normalizer_iff.mp (hNV z hzU) _).mp h2
  have e : x * z * x⁻¹ * z⁻¹ = z * (z⁻¹ * (x * z * x⁻¹)) * z⁻¹ := by group
  rw [e]
  exact h3


theorem ggL45_conj_V_mem_of_moving (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hmov : ∀ n ∈ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
      n ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
      ∀ v ∈ U ⊓ Subgroup.centralizer (K : Set G), n * v * n⁻¹ ∈ U₁) {n : G}
    (hn : n ∈ Subgroup.normalizer (U : Set G) ⊓
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G))
    {v : G} (hv : v ∈ U ⊓ Subgroup.centralizer (K : Set G)) : n * v * n⁻¹ ∈ U₁ := by
  obtain ⟨-, -, hVU₁⟩ := ggL4546_basic hraw hiso hcfg
  by_cases hnd : n ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)
  · have hnK := ggL45_normalizer_le_of_canonical hcfg.1 hcfg.2.2.2.2.2.1 ⟨hn.2, hnd⟩
    refine hVU₁ ⟨(Subgroup.mem_normalizer_iff.mp hn.1 v).mp hv.1, ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (ggNormalizer_le_normalizer_centralizer K hnK) v).mp
      hv.2
  · exact hmov n hn hnd v hv


end Moving


end CFSG.StandardType

end
