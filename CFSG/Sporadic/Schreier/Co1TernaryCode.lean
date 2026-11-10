module

public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public import Certificates.Certificate2149

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix

@[expose] def codeRightInv : Matrix (Fin 12) (Fin 6) (ZMod 3) :=
  !![1, 0, 1, 1, 1, 1; 1, 0, 0, 1, 2, 2; 1, 1, 0, 2, 0, 0; 0, 0, 0, 2, 2, 0; 1, 1, 2, 0, 1, 0;
    0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0]

@[expose] def codeProj : Matrix (Fin 12) (Fin 6) (ZMod 3) :=
  !![0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0;
    1, 0, 0, 2, 1, 0; 0, 0, 0, 0, 0, 0; 1, 1, 1, 2, 1, 2; 2, 1, 2, 0, 0, 1; 2, 0, 0, 1, 1, 1;
    0, 0, 2, 2, 2, 2; 1, 1, 1, 2, 1, 0]


theorem γ_zero : ∀ j, γ j 0 = 1 := by decide

theorem R_zero : R 0 = fun _ => 1 := by
  funext j
  revert j
  decide

theorem R_mul_codeRightInv : R * codeRightInv = 1 := by decide

theorem R_mul_transpose : R * Rᵀ = 0 := by decide

theorem codeProj_decomp : codeProj * R + Rᵀ * codeRightInvᵀ = 1 := by decide

theorem mem_T_iff (v : Fin 12 → ZMod 3) : v ∈ T ↔ ∃ b : Fin 6 → ZMod 3, b ᵥ* R = v := by
  have h := Submodule.mem_span_range_iff_exists_fun (ZMod 3)
    (v := fun i : Fin 6 => (R i : Fin 12 → ZMod 3)) (x := v)
  simp only [vecMul_eq_sum]
  exact h


theorem vecMul_R_injective : Function.Injective fun b : Fin 6 → ZMod 3 => b ᵥ* R := by
  intro b c h
  have h' : b ᵥ* R = c ᵥ* R := h
  rw [← vecMul_one b, ← vecMul_one c, ← R_mul_codeRightInv, ← vecMul_vecMul, ← vecMul_vecMul, h']

theorem range_vecMulLinear_R : LinearMap.range (vecMulLinear R) = T := by
  ext v
  rw [LinearMap.mem_range, mem_T_iff]
  simp only [vecMulLinear_apply]

@[expose] noncomputable def codeEquiv : (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] T :=
  (LinearEquiv.ofInjective (vecMulLinear R) vecMul_R_injective).trans
    (LinearEquiv.ofEq _ _ range_vecMulLinear_R)


theorem finrank_T : Module.finrank (ZMod 3) T = 6 := by
  rw [← codeEquiv.finrank_eq, Module.finrank_fin_fun]

@[expose] noncomputable def eCode : E ≃* Multiplicative T :=
  eEquiv.symm.trans (AddEquiv.toMultiplicative codeEquiv.toAddEquiv)


theorem mem_T_iff_orthogonal (v : Fin 12 → ZMod 3) : v ∈ T ↔ ∀ w ∈ T, v ⬝ᵥ w = 0 := by
  constructor
  · intro hv w hw
    obtain ⟨b, rfl⟩ := (mem_T_iff v).mp hv
    obtain ⟨c, rfl⟩ := (mem_T_iff w).mp hw
    rw [← mulVec_transpose R c, dotProduct_mulVec, vecMul_vecMul, R_mul_transpose, vecMul_zero,
      zero_dotProduct]
  · intro h
    have h0 : v ᵥ* Rᵀ = 0 := by
      rw [vecMul_transpose]
      funext i
      rw [Pi.zero_apply]
      change (fun j => R i j) ⬝ᵥ v = 0
      rw [dotProduct_comm]
      exact h (R i) (Submodule.subset_span ⟨i, rfl⟩)
    refine (mem_T_iff v).mpr ⟨v ᵥ* codeProj, ?_⟩
    have := congrArg (fun M => v ᵥ* M) codeProj_decomp
    simp only [vecMul_add, vecMul_one, ← vecMul_vecMul, h0, zero_vecMul, add_zero] at this
    exact this


theorem ones_mem_T : (fun _ => 1 : Fin 12 → ZMod 3) ∈ T := by
  rw [← R_zero]
  exact Submodule.subset_span ⟨0, rfl⟩

end CFSG.Sporadic.Co1Schreier
