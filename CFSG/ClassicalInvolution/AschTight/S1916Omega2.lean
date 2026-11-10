module

public import CFSG.ClassicalInvolution.AschTight.S1916Local

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G]


theorem conj_mem_centralizer_iff {z g x : G} :
    x ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G) ↔
      g⁻¹ * x * g ∈ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [h]
      _ = z * (g⁻¹ * x * g) := by group
  · intro h
    calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = g * z * g⁻¹ * x := by group

theorem centralizer_le_normalizer_conjSub {M : Subgroup G} {z : G}
    (hM : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (M : Set G)) (g : G) :
    Subgroup.centralizer ({g * z * g⁻¹} : Set G) ≤
      Subgroup.normalizer ((conjSub g M : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_normalizer_conjSub_iff]
  exact hM (conj_mem_centralizer_iff.mp hx)

theorem conjSub_eq_of_conj_eq {M : Subgroup G} {z g h : G}
    (hM : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (M : Set G))
    (hgh : g * z * g⁻¹ = h * z * h⁻¹) : conjSub g M = conjSub h M := by
  have h1 : h⁻¹ * g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc h⁻¹ * g * z = h⁻¹ * (g * z * g⁻¹) * g := by group
      _ = h⁻¹ * (h * z * h⁻¹) * g := by rw [hgh]
      _ = z * (h⁻¹ * g) := by group
  have h2 : conjSub (h⁻¹ * g) M = M := mem_normalizer_iff_conjSub_eq.mp (hM h1)
  calc conjSub g M = conjSub h (conjSub (h⁻¹ * g) M) := by rw [← conjSub_mul, mul_inv_cancel_left]
    _ = conjSub h M := by rw [h2]

variable {p f : ℕ} [Fact p.Prime] [Finite G]


theorem exists_involution_of_two_dvd {H : Subgroup G} (h2 : 2 ∣ Nat.card H) :
    ∃ y ∈ H, y * y = 1 ∧ y ≠ 1 := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have htG : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  refine ⟨t, t.2, ?_, ?_⟩
  · have := pow_orderOf_eq_one (t : G)
    rwa [htG, pow_two] at this
  · intro h
    rw [h, orderOf_one] at htG
    omega


end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
