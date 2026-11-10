module

public import CFSG.Adapters.TauCetiExceptional.MinusculeMatch
public import CFSG.Open.LocalVocabulary

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg

section NatMat

variable {d : ℕ} (R : Type*) [CommRing R]

@[expose] def natMat : Module.End R (Fin d →₀ R) ≃ₐ[R] Matrix (Fin d) (Fin d) R :=
  LinearMap.toMatrixAlgEquiv Finsupp.basisSingleOne

theorem natMat_apply (f : Module.End R (Fin d →₀ R)) (r s : Fin d) :
    natMat R f r s = f (Finsupp.single s 1) r := by
  simp [natMat, LinearMap.toMatrixAlgEquiv_apply]


end NatMat

variable {τ : Tag} (D : MinData τ)

@[expose] def rootMat (γ : Fin τ.rank → ℤ) : Matrix (Fin D.d) (Fin D.d) ℤ :=
  natMat ℤ (D.rootOp ℤ γ)

theorem rootOp_single_apply_eq_cast
    (R : Type*) [CommRing R] (γ : Fin τ.rank → ℤ)
    (r s : Fin D.d) :
    D.rootOp R γ (Finsupp.single s 1) r = ((D.rootOp ℤ γ (Finsupp.single s 1) r : ℤ) : R) := by
  classical
  unfold MinData.rootOp
  split_ifs with h
  · simp only [MinData.E, toEnd_single, digVec]
    split_ifs with h'
    · simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
      split_ifs <;> push_cast <;> ring
    · simp
  · simp

theorem natMat_rootOp
    (R : Type*) [CommRing R] (γ : Fin τ.rank → ℤ) :
    natMat R (D.rootOp R γ) = (rootMat D γ).map (Int.cast : ℤ → R) := by
  ext r s
  rw [natMat_apply, Matrix.map_apply, rootMat, natMat_apply, rootOp_single_apply_eq_cast]

variable {D} (hV : D.Valid)

theorem natMat_rootUnit
    (R : Type*) [CommRing R] (γ : Fin τ.rank → ℤ) (c : R) :
    natMat R (rootUnit hV R γ c : Module.End R (Fin D.d →₀ R)) =
      1 + c • (rootMat D γ).map (Int.cast : ℤ → R) := by
  rw [coe_rootUnit, map_add, map_one, map_smul, natMat_rootOp]


section Uni

variable {R : Type*} [CommRing R] {n : ℕ}

structure IsUpperUni (M : Matrix (Fin n) (Fin n) R) : Prop where
  diag : ∀ i, M i i = 1
  lower : ∀ i j, j < i → M i j = 0

structure IsLowerUni (M : Matrix (Fin n) (Fin n) R) : Prop where
  diag : ∀ i, M i i = 1
  upper : ∀ i j, i < j → M i j = 0


theorem IsUpperUni.mul {M N : Matrix (Fin n) (Fin n) R} (hM : IsUpperUni M)
    (hN : IsUpperUni N) : IsUpperUni (M * N) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hM.diag, hN.diag, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hM.lower i k h, zero_mul]
      · rw [hN.lower k i h, mul_zero]
    · simp
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with h | h
    · rw [hM.lower i k h, zero_mul]
    · rw [hN.lower k j (lt_of_lt_of_le hij h), mul_zero]

theorem IsLowerUni.mul {M N : Matrix (Fin n) (Fin n) R} (hM : IsLowerUni M)
    (hN : IsLowerUni N) : IsLowerUni (M * N) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hM.diag, hN.diag, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hN.upper k i h, mul_zero]
      · rw [hM.upper i k h, zero_mul]
    · simp
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge i k with h | h
    · rw [hM.upper i k h, zero_mul]
    · rw [hN.upper k j (lt_of_le_of_lt h hij), mul_zero]

end Uni

@[expose] def DegOrdered (D : MinData τ) : Prop :=
  ∀ a b : Fin D.d, a ≤ b → D.deg b ≤ D.deg a


end CFSG.TauCetiBridge.Minuscule
