module

public import CFSG.HardMathSupport.Foote.E27.LieTwo.MatTable
public import CFSG.Assembly.Defs

public section

namespace CFSG.HardMathSupport.Foote.E27

open Matrix Subgroup CFSG.Sporadic.He.Native

@[expose] def FpfM {d : ℕ} (M : M2 d) : Prop := ∀ v : Fin d → ZMod 2, M *ᵥ v = v → v = 0

@[expose] instance {d : ℕ} (M : M2 d) : Decidable (FpfM M) := by
  unfold FpfM; infer_instance


theorem factorization_three_of_eq {n k m : ℕ} (h : n = 3 ^ k * m) (hm : ¬ 3 ∣ m) :
    n.factorization 3 = k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 3)
  rw [h, Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem fpfM_conj_mp {d : ℕ} {G : Type*} [Group G] (mat : G →* M2 d) (g x : G)
    (h : FpfM (mat x)) : FpfM (mat (g * x * g⁻¹)) := by
  intro w hw
  have hinv : mat g⁻¹ * mat g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hinv' : mat g * mat g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have this' : (mat g * mat x * mat g⁻¹) *ᵥ w = w := by
    have := hw
    rwa [map_mul, map_mul] at this
  have h1 : mat x *ᵥ (mat g⁻¹ *ᵥ w) = mat g⁻¹ *ᵥ w := by
    calc mat x *ᵥ (mat g⁻¹ *ᵥ w)
        = (mat g⁻¹ * mat g) *ᵥ (mat x *ᵥ (mat g⁻¹ *ᵥ w)) := by rw [hinv, Matrix.one_mulVec]
      _ = mat g⁻¹ *ᵥ ((mat g * mat x * mat g⁻¹) *ᵥ w) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = mat g⁻¹ *ᵥ w := by rw [this']
  have h3 := h _ h1
  have : w = mat g *ᵥ (mat g⁻¹ *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
  rw [this, h3, Matrix.mulVec_zero]

theorem fpfM_conj {d : ℕ} {G : Type*} [Group G] (mat : G →* M2 d) (g x : G) :
    FpfM (mat (g * x * g⁻¹)) = FpfM (mat x) := by
  apply propext
  refine ⟨fun h => ?_, fpfM_conj_mp mat g x⟩
  have := fpfM_conj_mp mat g⁻¹ _ h
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at this

section Spec


end Spec

end CFSG.HardMathSupport.Foote.E27
