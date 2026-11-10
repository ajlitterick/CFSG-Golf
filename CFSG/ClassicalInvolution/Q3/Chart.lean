module

public import CFSG.ClassicalInvolution.Q3.Basic
public import CFSG.ClassicalInvolution.Balance.WeakFrame.Member
public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups

section Involutions

private def elemT : SL(2, ZMod 3) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩


end Involutions

section Member

variable {G : Type} [Group G] {K : Subgroup G} {z : G}

theorem IsClassicalMember3.isCentralInvolution (h : IsClassicalMember3 K z) :
    IsCentralInvolution K z where
  mem := h.mem
  ne_one := h.ne_one
  sq := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [h.orderOf_eq_two])
  central := by
    intro k hk
    have := CFSG.ClassicalInvolution.isSubnormal_le h.subnormal hk
    exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm

end Member

section Chart

variable {G : Type} [Group G] {K : Subgroup G}

structure IsChart3 (K : Subgroup G) (φ : ↥K →* SL(2, ZMod 3)) : Prop where
  surjective : Function.Surjective φ
  ker_eq : φ.ker = classicalInvolutionOddCore ↥K

namespace IsChart3

variable {φ : ↥K →* SL(2, ZMod 3)} {z : G}

theorem map_central [Finite G] (hφ : IsChart3 K φ) (hz : IsCentralInvolution K z) :
    φ ⟨z, hz.mem⟩ = -1 := by
  have hz1 : (⟨z, hz.mem⟩ : ↥K) * ⟨z, hz.mem⟩ = 1 := Subtype.ext hz.sq
  have hcen : φ ⟨z, hz.mem⟩ ∈ Subgroup.center SL(2, ZMod 3) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := hφ.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (hz.central k k.2).symm)
  rcases (mem_center_sl2_iff _).mp hcen with h | h
  · exfalso
    have hmem : (⟨z, hz.mem⟩ : ↥K) ∈ classicalInvolutionOddCore ↥K := by
      rw [← hφ.ker_eq]
      exact h
    exact hz.ne_one (congrArg Subtype.val (eq_one_of_mem_oddCore_of_sq hmem hz1))
  · exact h

theorem eq_of_central [Finite G] (hφ : IsChart3 K φ) {z' : G} (hz : IsCentralInvolution K z)
    (hz' : IsCentralInvolution K z') : z = z' := by
  have h1 := hφ.map_central hz
  have h2 := hφ.map_central hz'
  have hprod : φ (⟨z, hz.mem⟩ * ⟨z', hz'.mem⟩) = 1 := by
    rw [map_mul, h1, h2]
    have := mul_inv_cancel (-1 : SL(2, ZMod 3))
    rwa [neg_one_inv] at this
  have hmem : (⟨z, hz.mem⟩ * ⟨z', hz'.mem⟩ : ↥K) ∈ classicalInvolutionOddCore ↥K := by
    rw [← hφ.ker_eq]
    exact hprod
  have hsq : (⟨z, hz.mem⟩ * ⟨z', hz'.mem⟩ : ↥K) * (⟨z, hz.mem⟩ * ⟨z', hz'.mem⟩) = 1 := by
    apply Subtype.ext
    show z * z' * (z * z') = 1
    calc z * z' * (z * z') = z * (z' * z) * z' := by group
      _ = z * (z * z') * z' := by rw [hz.central z' hz'.mem]
      _ = (z * z) * (z' * z') := by group
      _ = 1 := by rw [hz.sq, hz'.sq, one_mul]
  have h3 := eq_one_of_mem_oddCore_of_sq hmem hsq
  have h4 : z * z' = 1 := congrArg Subtype.val h3
  calc z = z * (z' * z') := by rw [hz'.sq, mul_one]
    _ = (z * z') * z' := (mul_assoc _ _ _).symm
    _ = z' := by rw [h4, one_mul]

theorem eq_one_or_eq_of_sq [Finite G] (hφ : IsChart3 K φ) (hz : IsCentralInvolution K z) {x : G}
    (hx : x ∈ K) (hsq : x * x = 1) : x = 1 ∨ x = z := by
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hx1 : (⟨x, hx⟩ : ↥K) * ⟨x, hx⟩ = 1 := Subtype.ext hsq
  have hφsq : φ ⟨x, hx⟩ * φ ⟨x, hx⟩ = 1 := by rw [← map_mul, hx1, map_one]
  rcases sl2_sq_eq_one h2 hφsq with h | h
  · left
    have hmem : (⟨x, hx⟩ : ↥K) ∈ classicalInvolutionOddCore ↥K := by
      rw [← hφ.ker_eq]
      exact h
    exact congrArg Subtype.val (eq_one_of_mem_oddCore_of_sq hmem hx1)
  · right
    have hz1 := hφ.map_central hz
    have hxz : x * z = z * x := (hz.central x hx).symm
    have hprod : φ (⟨x, hx⟩ * ⟨z, hz.mem⟩) = 1 := by
      rw [map_mul, h, hz1]
      have := mul_inv_cancel (-1 : SL(2, ZMod 3))
      rwa [neg_one_inv] at this
    have hmem : (⟨x, hx⟩ * ⟨z, hz.mem⟩ : ↥K) ∈ classicalInvolutionOddCore ↥K := by
      rw [← hφ.ker_eq]
      exact hprod
    have hsq' : (⟨x, hx⟩ * ⟨z, hz.mem⟩ : ↥K) * (⟨x, hx⟩ * ⟨z, hz.mem⟩) = 1 := by
      apply Subtype.ext
      show x * z * (x * z) = 1
      calc x * z * (x * z) = x * (z * x) * z := by group
        _ = x * (x * z) * z := by rw [← hxz]
        _ = (x * x) * (z * z) := by group
        _ = 1 := by rw [hsq, hz.sq, one_mul]
    have h3 := eq_one_of_mem_oddCore_of_sq hmem hsq'
    have h4 : x * z = 1 := congrArg Subtype.val h3
    calc x = x * (z * z) := by rw [hz.sq, mul_one]
      _ = (x * z) * z := (mul_assoc _ _ _).symm
      _ = z := by rw [h4, one_mul]

end IsChart3

end Chart

end CFSG.ClassicalInvolution.Q3
