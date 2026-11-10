module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets
public import CFSG.ClassicalInvolution.AschTight.Thm6Tight

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G]

theorem IsQuaternionSub.eq_of_mul_self_eq_one {P : Subgroup G} (hP : IsQuaternionSub P)
    {x y : G} (hx : x ∈ P) (hy : y ∈ P) (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) : x = y := by
  obtain ⟨a, b, ha4, -, hb2, hbab, hcl⟩ := hP
  have hconj : ∀ i : ℤ, b * a ^ i * b⁻¹ = a ^ (-i) := fun i => by
    rw [← _root_.conj_zpow, hbab, inv_zpow']
  have hconj' : ∀ i : ℤ, b⁻¹ * a ^ i * b = a ^ (-i) := fun i => by
    have h1 := hconj (-i)
    rw [neg_neg] at h1
    calc b⁻¹ * a ^ i * b = b⁻¹ * (b * a ^ (-i) * b⁻¹) * b := by rw [h1]
      _ = a ^ (-i) := by group
  have hbN : b ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [hconj]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _
    · intro hw
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hw
      have e : w = b⁻¹ * a ^ i * b := by rw [hi]; group
      rw [e, hconj']
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _
  have hN2 : a ^ (orderOf a / 2) ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by omega) (by omega)
  have hinA : ∀ w ∈ P, w * w = 1 → w ∈ Subgroup.zpowers a := by
    intro w hw hw2
    rw [← hcl, closure_pair_eq_sup_zpowers] at hw
    have hw' : w ∈ ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := hw
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (Subgroup.zpowers_le.mpr hbN)] at hw'
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hw'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hb2' : b ^ (2 : ℤ) = a ^ ((orderOf a / 2 : ℕ) : ℤ) := by
      rw [zpow_two, hb2, zpow_natCast]
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [← two_mul, zpow_mul, hb2', ← zpow_mul]
      exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _)
        (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _)
    · exfalso
      apply hN2
      have hw_eq : a ^ i * b ^ (2 * m + 1) = a ^ (i + ((orderOf a / 2 : ℕ) : ℤ) * m) * b := by
        rw [zpow_add_one, zpow_mul, hb2', ← zpow_mul, ← mul_assoc, ← zpow_add]
      rw [hw_eq] at hw2
      have e : ∀ j : ℤ, a ^ j * b * (a ^ j * b) = b * b := fun j => by
        calc a ^ j * b * (a ^ j * b) = a ^ j * (b * a ^ j * b⁻¹) * (b * b) := by group
          _ = b * b := by rw [hconj, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
      rw [e, hb2] at hw2
      exact hw2
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hinA x hx hx2)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hinA y hy hy2)
  exact zpow_eq_zpow_of_mul_self_eq_one hx2 hy2 hx1 hy1

theorem mem_normalizer_oddCoreOf_of_mem_normalizer [Finite G] {K : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    n ∈ Subgroup.normalizer (oddCoreOf K : Set G) := by
  have key : ∀ m ∈ Subgroup.normalizer (K : Set G), ∀ x ∈ oddCoreOf K,
      m * x * m⁻¹ ∈ oddCoreOf K := by
    intro m hm x hx
    obtain ⟨o, ho, rfl⟩ := hx
    let φ := normalizerConj K ⟨m, hm⟩
    have hnormal : ((classicalInvolutionOddCore ↥K).map φ.toMonoidHom).Normal :=
      Subgroup.Normal.map (classicalInvolutionOddCore_normal ↥K) φ.toMonoidHom φ.surjective
    have hodd : Odd (Nat.card ↥((classicalInvolutionOddCore ↥K).map φ.toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective φ.injective]
      exact CFSG.ComponentClassification.OddCore.odd_card ↥K
    have hle : (classicalInvolutionOddCore ↥K).map φ.toMonoidHom ≤
        classicalInvolutionOddCore ↥K := by
      unfold classicalInvolutionOddCore
      exact le_sSup ⟨hnormal, hodd⟩
    exact ⟨φ o, hle ⟨o, ho, rfl⟩, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key n hn x, fun hx => ?_⟩
  have := key n⁻¹ (Subgroup.inv_mem _ hn) _ hx
  rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this


end CFSG.ClassicalInvolution.Disconnected.AschTight
