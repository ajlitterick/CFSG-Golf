module

public import CFSG.Foundations.Basic
public import CFSG.GH74.GLS.Bg.TwoGroups.L23Models

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23 CFSG
open scoped commutatorElement

namespace UT3Aux

theorem mem_zpowers_iff_of_sq_eq_one {G : Type*} [Group G] {g : G} (h : g * g = 1) {x : G} :
    x ∈ Subgroup.zpowers g ↔ x = 1 ∨ x = g := by
  constructor
  · intro hx
    obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hk']
    have h2 : g ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h
    have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [hk, h0, add_zero, zpow_mul, h2, one_zpow]
    · right
      rw [hk, h1, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

@[expose] def omegaCoeff (x y : F4c) : ZMod 2 := (x * y).b

theorem omegaCoeff_add_left (x x' y : F4c) :
    omegaCoeff (x + x') y = omegaCoeff x y + omegaCoeff x' y := by
  revert x x' y; decide

theorem omegaCoeff_add_right (x y y' : F4c) :
    omegaCoeff x (y + y') = omegaCoeff x y + omegaCoeff x y' := by
  revert x y y'; decide

theorem omegaCoeff_zero_left (y : F4c) : omegaCoeff 0 y = 0 := by revert y; decide

theorem omegaCoeff_zero_right (x : F4c) : omegaCoeff x 0 = 0 := by revert x; decide

theorem F4c_add_self (x : F4c) : x + x = 0 := by revert x; decide

theorem zmod2_add_self (u : ZMod 2) : u + u = 0 := by revert u; decide

@[ext] structure Ext32 where
  a : F4c
  b : F4c
  s : ZMod 2

namespace Ext32

instance : DecidableEq Ext32 := fun x y =>
  decidable_of_iff (x.a = y.a ∧ x.b = y.b ∧ x.s = y.s) (by cases x; cases y; simp)

instance : Fintype Ext32 :=
  Fintype.ofEquiv (F4c × F4c × ZMod 2)
    { toFun := fun t => ⟨t.1, t.2.1, t.2.2⟩
      invFun := fun x => (x.a, x.b, x.s)
      left_inv := fun t => rfl
      right_inv := fun x => by cases x; rfl }

instance : Mul Ext32 := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.s + y.s + omegaCoeff x.a y.b⟩⟩

instance : One Ext32 := ⟨⟨0, 0, 0⟩⟩

instance : Inv Ext32 := ⟨fun x => ⟨x.a, x.b, x.s + omegaCoeff x.a x.b⟩⟩

theorem mul_def (x y : Ext32) :
    x * y = ⟨x.a + y.a, x.b + y.b, x.s + y.s + omegaCoeff x.a y.b⟩ := rfl

theorem one_def : (1 : Ext32) = ⟨0, 0, 0⟩ := rfl

theorem inv_def (x : Ext32) : x⁻¹ = ⟨x.a, x.b, x.s + omegaCoeff x.a x.b⟩ := rfl

instance : Group Ext32 where
  mul_assoc x y z := by
    refine Ext32.ext ?_ ?_ ?_
    · simp only [mul_def]; exact add_assoc _ _ _
    · simp only [mul_def]; exact add_assoc _ _ _
    · simp only [mul_def, omegaCoeff_add_left, omegaCoeff_add_right]; ring
  one_mul x := by
    refine Ext32.ext ?_ ?_ ?_
    · simp only [mul_def, one_def]; exact zero_add _
    · simp only [mul_def, one_def]; exact zero_add _
    · simp only [mul_def, one_def, omegaCoeff_zero_left]; ring
  mul_one x := by
    refine Ext32.ext ?_ ?_ ?_
    · simp only [mul_def, one_def]; exact add_zero _
    · simp only [mul_def, one_def]; exact add_zero _
    · simp only [mul_def, one_def, omegaCoeff_zero_right]; ring
  inv_mul_cancel x := by
    refine Ext32.ext ?_ ?_ ?_
    · simp only [mul_def, one_def, inv_def]; exact F4c_add_self _
    · simp only [mul_def, one_def, inv_def]; exact F4c_add_self _
    · simp only [mul_def, one_def, inv_def]
      calc x.s + omegaCoeff x.a x.b + x.s + omegaCoeff x.a x.b
          = (x.s + x.s) + (omegaCoeff x.a x.b + omegaCoeff x.a x.b) := by ring
        _ = 0 := by rw [zmod2_add_self, zmod2_add_self, add_zero]

@[expose] def z : Ext32 := ⟨0, 0, 1⟩

theorem mul_self_z : z * z = 1 := by decide

theorem z_ne_one : z ≠ 1 := by decide


theorem mem_center_iff (x : Ext32) : x ∈ Subgroup.center Ext32 ↔ x.a = 0 ∧ x.b = 0 := by
  rw [Subgroup.mem_center_iff]
  revert x
  decide


theorem card_eq : Nat.card Ext32 = 2 ^ 5 := by
  rw [Nat.card_eq_fintype_card]; decide

theorem orderOf_z : orderOf z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact mul_self_z) z_ne_one


end Ext32

@[expose] def proj : UT3 F4c →* Ext32 :=
  MonoidHom.mk' (fun x => ⟨x.a, x.b, x.c.b⟩) (fun _ _ => rfl)


theorem proj_surjective : Function.Surjective proj := fun y => ⟨⟨y.a, y.b, ⟨0, y.s⟩⟩, rfl⟩

theorem ker_proj : proj.ker = Subgroup.zpowers (⟨0, 0, 1⟩ : UT3 F4c) := by
  ext x
  rw [MonoidHom.mem_ker, mem_zpowers_iff_of_sq_eq_one
    (by decide : (⟨0, 0, 1⟩ : UT3 F4c) * ⟨0, 0, 1⟩ = 1)]
  revert x
  decide

end UT3Aux


end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
