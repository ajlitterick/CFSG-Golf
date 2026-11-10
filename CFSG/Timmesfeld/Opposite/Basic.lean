module

public import CFSG.Timmesfeld.RootSubgroupClosure

public section

namespace CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}


theorem opposite_conj_self (hD : IsRootInvolutionSet D) {d x : G} (hd : d ∈ D) (hx : x * x = 1)
    (hdx : ¬ Commute d x) (hodd : Odd (orderOf (d * x))) :
    ¬ Commute d (x * d * x⁻¹) ∧ Odd (orderOf (d * (x * d * x⁻¹))) := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hdd := hD.mul_self_eq_one hd
  have hsq : d * (x * d * x⁻¹) = (d * x) ^ 2 := by rw [hxinv, pow_two]; group
  have hord : orderOf (d * (x * d * x⁻¹)) = orderOf (d * x) := by
    rw [hsq, orderOf_pow' _ two_ne_zero, Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1
      ((Nat.coprime_two_left).2 hodd)), Nat.div_one]
  refine ⟨fun h => hdx ?_, hord ▸ hodd⟩
  have hee : x * d * x⁻¹ * (x * d * x⁻¹) = 1 := by
    rw [show x * d * x⁻¹ * (x * d * x⁻¹) = x * (d * d) * x⁻¹ by group, hdd, mul_one,
      mul_inv_cancel]
  have h2 := (commute_iff_mul_sq_eq_one hdd hee).1 h
  rw [hsq, ← pow_mul] at h2
  have h4 := orderOf_dvd_of_pow_eq_one h2
  have hle := Nat.le_of_dvd (by norm_num) h4
  have h1 : orderOf (d * x) = 1 := by
    obtain ⟨k, hk⟩ := hodd
    interval_cases h : orderOf (d * x) <;> omega
  have : d * x = 1 := orderOf_eq_one_iff.mp h1
  rw [eq_inv_of_mul_eq_one_left this, hxinv]


@[expose] noncomputable def dihedralSwap (t s : G) : G :=
  t * (t * s) ^ (orderOf (t * s) / 2 + 1)

theorem mul_pow_mul_eq_inv {t s : G} (ht : t * t = 1) (hs : s * s = 1) (m : ℕ) :
    t * (t * s) ^ m * t = ((t * s) ^ m)⁻¹ := by
  have h := mul_zpow_mul_eq_zpow_neg_mul ht hs (m : ℤ)
  rw [zpow_natCast, zpow_neg, zpow_natCast] at h
  rw [h, mul_assoc, ht, mul_one]

theorem dihedralSwap_mul_self {t s : G} (ht : t * t = 1) (hs : s * s = 1) :
    dihedralSwap t s * dihedralSwap t s = 1 := by
  rw [dihedralSwap]
  set m := orderOf (t * s) / 2 + 1
  rw [show t * (t * s) ^ m * (t * (t * s) ^ m) = t * (t * s) ^ m * t * (t * s) ^ m by group,
    mul_pow_mul_eq_inv ht hs, inv_mul_cancel]

theorem dihedralSwap_conj {t s : G} (ht : t * t = 1) (hs : s * s = 1)
    (hodd : Odd (orderOf (t * s))) : dihedralSwap t s * t * (dihedralSwap t s)⁻¹ = s := by
  obtain ⟨k, hk⟩ := hodd
  have hinv : (dihedralSwap t s)⁻¹ = dihedralSwap t s :=
    inv_eq_of_mul_eq_one_right (dihedralSwap_mul_self ht hs)
  have hk2 : orderOf (t * s) / 2 = k := by omega
  rw [hinv, dihedralSwap, hk2]
  have h1 : t * (t * s) ^ (k + 1) * t * (t * (t * s) ^ (k + 1)) =
      t * (t * s) ^ (k + 1) * (t * s) ^ (k + 1) := by
    rw [show t * (t * s) ^ (k + 1) * t * (t * (t * s) ^ (k + 1)) =
      t * (t * s) ^ (k + 1) * (t * t) * (t * s) ^ (k + 1) by group, ht, mul_one]
  rw [h1, mul_assoc, ← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hk,
    pow_orderOf_eq_one, one_mul, ← mul_assoc, ht, one_mul]

theorem dihedralSwap_conj' {t s : G} (ht : t * t = 1) (hs : s * s = 1)
    (hodd : Odd (orderOf (t * s))) : dihedralSwap t s * s * (dihedralSwap t s)⁻¹ = t := by
  have h := dihedralSwap_conj ht hs hodd
  have hrr := dihedralSwap_mul_self ht hs
  set r := dihedralSwap t s
  have hinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
  rw [← h, hinv, show r * (r * t * r) * r = (r * r) * t * (r * r) by group, hrr, one_mul,
    mul_one]


end CFSG.Timmesfeld
