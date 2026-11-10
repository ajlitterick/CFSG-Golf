module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalOrthogonalLagrangianDim
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalBasic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalRealization
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataFaithful
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags

public section

namespace CFSG.SeitzReduction

namespace OrthogonalLagrangian

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Involution

variable {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem isLagrangianDisplacement_of_involution {s : V ≃ₗ[K] V}
    (hsQ : ∀ v, Q (s v) = Q v) (hss : ∀ v, s (s v) = v)
    (hlag : LinearMap.ker ((s : V →ₗ[K] V) - 1) ≤ LinearMap.range ((s : V →ₗ[K] V) - 1)) :
    IsLagrangianDisplacement Q ((s : V →ₗ[K] V) - 1) := by
  have hN : ∀ x, ((s : V →ₗ[K] V) - 1) x = s x - x := fun x => rfl
  have hpol : ∀ x y, polar Q (s x) (s y) = polar Q x y := fun x y => by
    rw [polar, polar, ← map_add, hsQ, hsQ, hsQ]
  have hpol' : ∀ x y, polar Q (s x) y = polar Q x (s y) := fun x y => by
    rw [← hpol x (s y), hss]
  refine ⟨fun x => ?_, fun x y => ?_, fun x => ?_, fun x hx => ?_⟩
  · rw [hN, hN, map_sub, hss, vec_sub_eq_add K, vec_sub_eq_add K, vec_sub_eq_add K]
    have h := vec_add_self_eq_zero K (s x)
    have h' := vec_add_self_eq_zero K x
    calc x + s x + (s x + x) = (s x + s x) + (x + x) := by abel
      _ = 0 := by rw [h, h', add_zero]
  · rw [hN, hN, polar_sub_left, polar_sub_right, hpol']
  · rw [hN, vec_sub_eq_add K, QuadraticMap.map_add Q (s x) x, hsQ, polar_add_right,
      QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero, zero_add, add_zero,
      polar_comm]
  · obtain ⟨y, hy⟩ := hlag (LinearMap.mem_ker.mpr hx)
    exact ⟨y, hy⟩

end Involution

variable {K : Type} [Field K] {d : ℕ}

@[expose] noncomputable def isometryKappa (Q : QuadraticForm K (Fin d → K)) :
    matrixIsometries Q →* MulAut (matrixProjectiveDerived Q) :=
  (matrixProjectiveConjugationHom Q).comp (matrixIsometryInclusion Q)


section Model

variable [Finite K] [CharP K 2] {Q : QuadraticForm K (Fin d → K)}

theorem sq_eq_one_of_lagrangian (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hd : 8 ≤ d) (s : matrixIsometries Q) (hs : s * s = 1)
    (hlag : LinearMap.ker ((matrixLinearEquiv s.val : (Fin d → K) →ₗ[K] (Fin d → K)) - 1) ≤
      LinearMap.range ((matrixLinearEquiv s.val : (Fin d → K) →ₗ[K] (Fin d → K)) - 1))
    {β : MulAut (matrixProjectiveDerived Q)} (hβE : β ∈ matrixProjectiveImage Q)
    (hβs : β * isometryKappa Q s = isometryKappa Q s * β)
    (hβD : ∀ c, isometryKappa Q s c = c → Odd (orderOf c) → β c = c) : β ^ 2 = 1 := by
  have hd1 : 1 ≤ d := by omega
  have hscal : matrixDerivedScalars Q = ⊥ :=
    matrixDerivedScalars_eq_bot_of_charTwo Q (exists_ne_zero_of_polar_nondegenerate hd1 hQ)
  have hβE' : β ∈ (unitKappa Q).range := by
    rw [range_unitKappa Q]
    exact hβE
  obtain ⟨x, rfl⟩ := hβE'
  set T := coordinateSemilinearMap x.1.val with hTdef
  have hTs : ∀ (a : K) v, T (a • v) = x.1.val.right a • T v := fun a v =>
    coordinateSemilinearMap_smul x.1.val a v
  have hTQ : ∀ v, Q (T v) = x.1.val.right (Q v) := (mem_unitMultiplierPairs_iff Q x.1).mp x.2
  set sL := matrixLinearEquiv s.val with hsL
  have hsQ : ∀ v, Q (sL v) = Q v := (mem_matrixIsometries_iff Q s.val).mp s.2
  have hss : ∀ v, sL (sL v) = v := fun v => by
    have h := congrArg (fun g : matrixIsometries Q => matrixLinearEquiv g.val v) hs
    simp only [Subgroup.coe_mul, matrixLinearEquiv_mul, LinearEquiv.mul_apply,
      OneMemClass.coe_one] at h
    rw [h]
    exact Matrix.one_mulVec v
  set N : (Fin d → K) →ₗ[K] (Fin d → K) := (sL : (Fin d → K) →ₗ[K] (Fin d → K)) - 1 with hNdef
  have hN : ∀ v, N v = sL v - v := fun v => rfl
  have hL : IsLagrangianDisplacement Q N := isLagrangianDisplacement_of_involution hsQ hss hlag
  have hinc : matrixIsometryInclusion Q s ∈ unitMultiplierPairs Q := fun v => by
    rw [matrixIsometryInclusion_val, coordinateSemilinearMap_inl]
    exact hsQ v
  have hcomm : x.1 * matrixIsometryInclusion Q s = matrixIsometryInclusion Q s * x.1 := by
    have h2 : matrixProjectiveConjugationHom Q
        ((matrixIsometryInclusion Q s * x.1) * (x.1 * matrixIsometryInclusion Q s)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul]
      change isometryKappa Q s * unitKappa Q x * (unitKappa Q x * isometryKappa Q s)⁻¹ = 1
      rw [hβs, mul_inv_cancel]
    have h3 := eq_one_of_kappa_eq_one Q hQ hT hE hd1
      (mul_mem (mul_mem hinc x.2) (inv_mem (mul_mem x.2 hinc))) h2
    exact (mul_inv_eq_one.mp h3).symm
  have hTsL : ∀ v, T (sL v) = sL (T v) := fun v => by
    have h5 := congrArg (fun y : similarityPairs Q => coordinateSemilinearMap y.val v) hcomm
    simp only [Subgroup.coe_mul, coordinateSemilinearMap_mul, matrixIsometryInclusion_val,
      coordinateSemilinearMap_inl] at h5
    exact h5
  have hTN : ∀ v, T (N v) = N (T v) := fun v => by rw [hN, hN, map_sub, hTsL]
  have hodd : ∀ g : (Fin d → K) ≃ₗ[K] (Fin d → K), g ∈ elementaryGroup Q →
      (∀ v, g (N v) = N (g v)) → g ^ 3 = 1 → ∀ v, T (g v) = g (T v) := by
    intro g hgE hgN hg3 v
    set G : GL (Fin d) K := matrixLinearIso.symm g with hG
    have hGv : ∀ w, matrixLinearEquiv G w = g w := fun w => by
      change matrixLinearIso G w = g w
      rw [hG, MulEquiv.apply_symm_apply]
    have hGD : G ∈ matrixDerived Q := by
      rw [CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer.mem_matrixDerived_iff,
        hG, MulEquiv.apply_symm_apply, hE]
      exact hgE
    set A : matrixDerived Q := ⟨G, hGD⟩ with hAdef
    have hgs : ∀ w, g (sL w) = sL (g w) := fun w => by
      have e1 : sL w = N w + w := by rw [hN]; abel
      have e2 : sL (g w) = N (g w) + g w := by rw [hN]; abel
      rw [e1, map_add, hgN, e2]
    have hfix : isometryKappa Q s (matrixProjectiveProjection Q A) =
        matrixProjectiveProjection Q A := by
      change matrixProjectiveConjugation Q (matrixIsometryInclusion Q s)
        (matrixProjectiveProjection Q A) = _
      rw [matrixProjectiveConjugation_mk]
      congr 1
      apply Subtype.ext
      rw [matrixDerivedConjugation_val]
      change s.val * CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut
        (Fin d) K 1 G * s.val⁻¹ = G
      rw [map_one, MulAut.one_apply, mul_inv_eq_iff_eq_mul]
      apply matrixLinearIso.injective
      rw [map_mul, map_mul]
      refine LinearEquiv.ext fun w => ?_
      change sL (matrixLinearEquiv G w) = matrixLinearEquiv G (sL w)
      rw [hGv, hGv, hgs]
    have hA3 : A ^ 3 = 1 := by
      apply Subtype.ext
      apply matrixLinearIso.injective
      rw [SubgroupClass.coe_pow, map_pow, OneMemClass.coe_one, map_one]
      change (matrixLinearIso (matrixLinearIso.symm g)) ^ 3 = 1
      rw [MulEquiv.apply_symm_apply, hg3]
    have hodd3 : Odd (orderOf (matrixProjectiveProjection Q A)) :=
      Odd.of_dvd_nat (by decide : Odd 3)
        (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hA3, map_one]))
    have hβc := hβD _ hfix hodd3
    change matrixProjectiveConjugation Q x.1 (matrixProjectiveProjection Q A) =
      matrixProjectiveProjection Q A at hβc
    rw [matrixProjectiveConjugation_mk] at hβc
    have hA : matrixDerivedConjugation Q x.1 A = A := by
      simp only [matrixProjectiveProjection, QuotientGroup.mk'_apply] at hβc
      have h1 := QuotientGroup.eq.mp hβc
      rw [hscal, Subgroup.mem_bot, inv_mul_eq_one] at h1
      exact h1
    have hA' : matrixConjugation x.1.val G = G := congrArg Subtype.val hA
    have h1 := matrixConjugation_vector x.1.val G (T v)
    rw [hA', ← hTdef, AddEquiv.symm_apply_apply] at h1
    rw [← hGv, ← hGv, h1]
  have hsq : ∀ a : K, IsSquare a := FiniteField.isSquare_of_char_two (ringChar.eq K 2)
  have hdim : 8 ≤ Module.finrank K (Fin d → K) := by rw [Module.finrank_fin_fun]; exact hd
  obtain ⟨-, hT2⟩ := semilinear_lagrangian_rigidity_of_finrank hsq hQ hdim hL T hTs hTQ hTN
    (fun u v hu hv huv w => hodd _ (leviPair_mem_elementaryGroup u v)
      (fun y => hL.leviPair_apply_N hu hv y) (hL.leviPair_pow_three hu hv huv) w)
    (fun u v hu hv huv w hw y => hodd _
      (mul_mem (mul_mem (eichler_mem_elementaryGroup Q _ _) (leviPair_mem_elementaryGroup u v))
        (inv_mem (eichler_mem_elementaryGroup Q _ _)))
      (fun z => by
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          IsLagrangianDisplacement.inv_apply_N (hL.eichler_apply_N hv hw),
          hL.leviPair_apply_N hu hv, hL.eichler_apply_N hv hw, LinearEquiv.mul_apply,
          LinearEquiv.mul_apply])
      (by rw [conj_pow, hL.leviPair_pow_three hu hv huv, mul_one, mul_inv_cancel]) y)
  have hx2 : x.1.val * x.1.val = 1 := by
    apply coordinateSemilinearHom_injective hd1
    change Multiplicative.ofAdd (coordinateSemilinearMap (x.1.val * x.1.val)) =
      Multiplicative.ofAdd (coordinateSemilinearMap 1)
    congr 1
    exact AddEquiv.ext fun v => by
      rw [coordinateSemilinearMap_mul, hT2, coordinateSemilinearMap_one]
  have hx2' : x ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext (Subtype.ext hx2)
  rw [← map_pow, hx2', map_one]


end Model

section Coordinates


end Coordinates

end OrthogonalLagrangian

end CFSG.SeitzReduction
