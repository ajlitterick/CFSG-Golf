module

public import CFSG.CharacterTheory.Semidihedral.DerivedAndIndexTwo
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.CharacterTheory.Semidihedral.ElementOrders

public section

namespace CFSG.Semidihedral

open CFSG.Open

theorem half_residue_val (n : ℕ) (hn : 3 ≤ n) :
    (half n : ZMod (modulus n)).val = half n := by
  apply ZMod.val_natCast_of_lt
  have hp : 0 < half n := pow_pos (by decide) _
  have hm := modulus_eq_two_mul_half (by omega : 2 ≤ n)
  omega

theorem z_mem_dihedralSubgroup (n : ℕ) (hn : 3 ≤ n) :
    z n ∈ dihedralSubgroup n := by
  rw [z_eq_element n hn, element_mem_dihedralSubgroup_iff n hn,
    half_residue_val n hn]
  obtain ⟨k, hk⟩ := half_even hn
  omega

theorem z_mem_quaternionSubgroup (n : ℕ) (hn : 3 ≤ n) :
    z n ∈ quaternionSubgroup n := by
  rw [z_eq_element n hn, element_mem_quaternionSubgroup_iff n hn,
    half_residue_val n hn, ZMod.val_zero]
  obtain ⟨k, hk⟩ := half_even hn
  omega

theorem involution_mem_dihedralSubgroup (n : ℕ) (hn : 3 ≤ n)
    (g : SemidihedralGroup n) (hg : orderOf g = 2) :
    g ∈ dihedralSubgroup n := by
  obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n hn).symm.surjective g
  change orderOf (element n hn i e) = 2 at hg
  change element n hn i e ∈ dihedralSubgroup n
  rcases exponent_cases e with rfl | rfl
  · rw [(rotation_involution_iff n hn i).mp hg, ← z_eq_element n hn]
    exact z_mem_dihedralSubgroup n hn
  · rw [element_mem_dihedralSubgroup_iff n hn]
    exact (outside_involution_iff n hn i).mp hg

theorem quaternion_unique_involution (n : ℕ) (hn : 3 ≤ n)
    (g : SemidihedralGroup n) (hQ : g ∈ quaternionSubgroup n)
    (hg : orderOf g = 2) : g = z n := by
  obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n hn).symm.surjective g
  change orderOf (element n hn i e) = 2 at hg
  change element n hn i e ∈ quaternionSubgroup n at hQ
  change element n hn i e = z n
  rw [element_mem_quaternionSubgroup_iff n hn] at hQ
  rcases exponent_cases e with rfl | rfl
  · rw [(rotation_involution_iff n hn i).mp hg, ← z_eq_element n hn]
  · have heven := (outside_involution_iff n hn i).mp hg
    simp only [ZMod.val_one_eq_one_mod, show (1 % 2 : ℕ) = 1 by decide] at hQ
    omega


theorem negative_quarter_eq_element (n : ℕ) (hn : 4 ≤ n) :
    r n ^ (-((2 ^ (n - 3) : ℕ) : ℤ)) =
      element n (by omega) (-((2 ^ (n - 3) : ℕ) : ZMod (modulus n))) 0 := by
  rw [r_zpow_eq_element n (by omega)]
  push_cast
  rfl

theorem dihedral_order_four_iff (n : ℕ) (hn : 4 ≤ n)
    (g : SemidihedralGroup n) (hg : g ∈ dihedralSubgroup n) :
    orderOf g = 4 ↔ g = r n ^ (2 ^ (n - 3)) ∨
      g = r n ^ (-((2 ^ (n - 3) : ℕ) : ℤ)) := by
  obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n (by omega)).symm.surjective g
  change element n (by omega) i e ∈ dihedralSubgroup n at hg
  change orderOf (element n (by omega) i e) = 4 ↔
    element n (by omega) i e = r n ^ (2 ^ (n - 3)) ∨
    element n (by omega) i e = r n ^ (-((2 ^ (n - 3) : ℕ) : ℤ))
  rw [element_mem_dihedralSubgroup_iff n (by omega)] at hg
  rw [r_pow_eq_element n (by omega), negative_quarter_eq_element n hn]
  rcases exponent_cases e with rfl | rfl
  · rw [rotation_order_four_iff n hn]
    simp only [element_eq_iff, eq_self, and_true]
  · rw [outside_order_four_iff n (by omega), hg]
    simp only [element_eq_iff, one_ne_zero, and_false, false_or]
    decide

theorem modulus_div_two (n : ℕ) (hn : 3 ≤ n) : modulus n / 2 = half n := by
  rw [modulus_eq_two_mul_half (by omega)]
  omega

theorem modulus_div_four (n : ℕ) (hn : 4 ≤ n) :
    modulus n / 4 = 2 ^ (n - 3) := by
  have hm : modulus n = 4 * 2 ^ (n - 3) := by
    rw [modulus_eq_two_mul_half (by omega), half_eq_two_mul_quarter (by omega)]
    ring
  omega


end CFSG.Semidihedral
