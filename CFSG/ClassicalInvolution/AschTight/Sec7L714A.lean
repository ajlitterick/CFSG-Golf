module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64E
public import CFSG.ClassicalInvolution.AschTight.Sec71Basic
public import CFSG.ClassicalInvolution.AschTight.Sec7KeyC
public import CFSG.ClassicalInvolution.AschTight.Sec7L76B

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isUniqueInvolution_zpowers {u : G} {k : ℕ} (hu : orderOf u = 2 ^ (k + 1)) :
    IsUniqueInvolution (Subgroup.zpowers u) (u ^ 2 ^ k) where
  mem := Subgroup.pow_mem _ (Subgroup.mem_zpowers u) _
  ne_one := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hu] at h1
    have h2 := Nat.le_of_dvd (by positivity) h1
    have h3 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  sq := by
    rw [← pow_add, ← two_mul, ← pow_succ', ← hu, pow_orderOf_eq_one]
  unique := by
    intro y hy hy2
    obtain ⟨c, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 : u ^ (2 * c) = 1 := by
      rw [two_mul, zpow_add]; exact hy2
    have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hu] at h2
    have h3 : ((2 : ℤ) ^ k) ∣ c := by
      have e : ((2 ^ (k + 1) : ℕ) : ℤ) = 2 * 2 ^ k := by push_cast; ring
      rw [e] at h2
      exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h2
    obtain ⟨m, rfl⟩ := h3
    have e : u ^ ((2 : ℤ) ^ k * m) = (u ^ 2 ^ k) ^ m := by
      rw [zpow_mul]; norm_cast
    rw [e]
    have hsq : u ^ 2 ^ k * u ^ 2 ^ k = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ', ← hu, pow_orderOf_eq_one]
    rcases Int.even_or_odd m with hm | hm
    · exact Or.inl (Sec71.zpow_eq_one_of_even hsq hm)
    · exact Or.inr (Sec71.zpow_eq_self_of_odd hsq hm)

theorem closure_pair_eq_sup (a b : G) :
    Subgroup.closure {a, b} = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
    Set.singleton_union]


end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
