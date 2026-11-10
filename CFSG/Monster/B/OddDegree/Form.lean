module

public import CFSG.Monster.B.Gen.MinkowskiTwo
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Data.Int.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Monster.B.OddDegree

open Matrix

section Integral

variable {G : Type*} [Group G] [Fintype G] {n : ℕ}


end Integral


section Reducible

variable {G : Type*} [Group G] {n : ℕ}

@[expose] def quadForm (B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := ∑ i, B i i * v i
  map_add' u v := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem zmod_two_sq (c : ZMod 2) : c * c = c := by fin_cases c <;> rfl

theorem zmod_two_add_self' (c : ZMod 2) : c + c = 0 := by fin_cases c <;> rfl

theorem dotProduct_mulVec_add {B : Matrix (Fin n) (Fin n) (ZMod 2)} (hB : Bᵀ = B)
    (u v : Fin n → ZMod 2) :
    (u + v) ⬝ᵥ (B *ᵥ (u + v)) = u ⬝ᵥ (B *ᵥ u) + v ⬝ᵥ (B *ᵥ v) := by
  have hcross : v ⬝ᵥ (B *ᵥ u) = u ⬝ᵥ (B *ᵥ v) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hB, dotProduct_comm]
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hcross]
  have h2 : u ⬝ᵥ (B *ᵥ v) + u ⬝ᵥ (B *ᵥ v) = 0 := zmod_two_add_self' _
  linear_combination h2

theorem dotProduct_mulVec_self {B : Matrix (Fin n) (Fin n) (ZMod 2)} (hB : Bᵀ = B)
    (v : Fin n → ZMod 2) : v ⬝ᵥ (B *ᵥ v) = quadForm B v := by
  let F : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun v => v ⬝ᵥ (B *ᵥ v)
      map_add' := dotProduct_mulVec_add hB
      map_smul' := fun c v => by
        simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
          RingHom.id_apply, ← mul_assoc, zmod_two_sq] }
  have hF : F = quadForm B := by
    refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
    simp only [F, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      LinearMap.coe_single, quadForm]
    rw [Matrix.mulVec_single_one, single_dotProduct, one_mul,
      Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
        (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, mul_one]
    rfl
  exact congrFun (congrArg DFunLike.coe hF) v


end Reducible

end CFSG.Monster.B.OddDegree
