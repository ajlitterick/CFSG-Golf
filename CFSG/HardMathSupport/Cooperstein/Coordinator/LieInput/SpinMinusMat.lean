module

public import CFSG.LieType.Steinberg.Classical.SpinFrame.Unipotent
public import CFSG.LieType.Universal.Spin.Twisted.Unipotent

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open Matrix QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Steinberg.SpinFrame

section Frame

variable (n : ℕ) {K : Type} [Field K] (b c : K)

theorem isCoordFrame_minusFrame :
    IsCoordFrame (minusFrame n b c).toHypFrame (minusPos n) where
  vec_eq m r := minusVec_eq_single n m r
  polar_eq v m r := polar_minusVec_eq_apply n v m r

variable {n b c}

theorem mat_longRoot_eq {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (a : K) :
    mat n ((minusFrame n b c).longRoot hij s t (.ofAdd a)) =
      1 + a • longMat K (minusPos n) i j s t :=
  coe_spinMatrix_longRoot (isCoordFrame_minusFrame n b c) hij s t a

end Frame


section Short

variable {n : ℕ} {K : Type} [Field K] (b c : K)

@[expose] noncomputable def polarVec (n : ℕ) (p : Fin 2 → K) :
    Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K :=
  fun e => polar (quadMinus n K b c) (Pi.single e 1) (planeVec n p)

@[expose] noncomputable def shortMat (n : ℕ) (i : Fin (n - 1)) (s : Bool) (p : Fin 2 → K) :
    Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K :=
  1 + Matrix.vecMulVec (planeVec n p) (Pi.single (minusPos n i (!s)) 1) -
    Matrix.vecMulVec (Pi.single (minusPos n i s) 1)
      (polarVec b c n p + planeNorm b c p • Pi.single (minusPos n i (!s)) 1)

variable {b c} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem mat_twShortRoot_eq (i : Fin (n - 1)) (s : Bool) (p : Fin 2 → K) :
    mat n (twShortRoot n hirr i s (.ofAdd p)) = shortMat b c n i s p := by
  ext a e
  rw [mat_twShortRoot_apply]
  simp only [shortMat, polarVec, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> (try subst_vars) <;> first | ring1 | (exfalso; simp_all)

end Short

section Faithful

variable {n : ℕ} {K : Type} [Field K] {b c : K}

theorem mat_injective [Finite K] [CharP K 2] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Function.Injective (mat n (K := K) (b := b) (c := c)) := by
  intro x y h
  have h2 : spinMatrix (quadMinus n K b c) x = spinMatrix (quadMinus n K b c) y := Units.ext h
  have hk := ker_spinMatrix_quadMinus_eq_bot (n := n) hirr (CharTwo.two_eq_zero)
  have : x⁻¹ * y ∈ (spinMatrix (quadMinus n K b c)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
  rw [hk, Subgroup.mem_bot] at this
  exact inv_mul_eq_one.mp this

theorem quad_mat_mulVec (g : spinGroup (quadMinus n K b c)) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    quadMinus n K b c (mat n g *ᵥ v) = quadMinus n K b c v :=
  spinMatrix_mem (quadMinus n K b c) g v

theorem polar_mat_mulVec (g : spinGroup (quadMinus n K b c))
    (v w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    polar (quadMinus n K b c) (mat n g *ᵥ v) (mat n g *ᵥ w) = polar (quadMinus n K b c) v w := by
  unfold QuadraticMap.polar
  rw [← Matrix.mulVec_add, quad_mat_mulVec, quad_mat_mulVec, quad_mat_mulVec]

end Faithful

section Torus

variable {n : ℕ} {K : Type} [Field K] {b c : K}


theorem single_inr_inr_eq_planeVec (u : Fin 2) :
    (Pi.single (.inr (.inr u)) 1 : Vm n K) = planeVec n (Pi.single u 1) := by
  funext x
  rcases x with k | k | t' <;> simp [planeVec, Pi.single_apply]


end Torus


section RootGroups


end RootGroups

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
