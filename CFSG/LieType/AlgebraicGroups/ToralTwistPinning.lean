module

public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningRoots
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycle
public import CFSG.LieType.Chevalley.LatticeCharacterInterpolation

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped CFSG.ConvolutionPoints

section Character

variable {τ : Tag} {k : Type} [Field k]

@[expose] def signCharTuple (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) : Fin τ.rank → kˣ :=
  fun i => intUnitsMap k (χ (Multiplicative.ofAdd (Pi.single i 1)))

theorem rootChar_signCharTuple (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ)
    (v : Fin τ.rank → ℤ) :
    rootChar (signCharTuple (k := k) χ) v = intUnitsMap k (χ (Multiplicative.ofAdd v)) := by
  have hv : Multiplicative.ofAdd v =
      ∏ i, Multiplicative.ofAdd (v i • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    rw [← ofAdd_sum]
    congr 1
    conv_lhs => rw [← Finset.univ_sum_single v]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [hv, map_prod, map_prod, rootChar]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofAdd_zsmul, map_zpow, map_zpow, signCharTuple]

theorem signCharTuple_sign (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) (i : Fin τ.rank) :
    signCharTuple (k := k) χ i = 1 ∨ signCharTuple (k := k) χ i = -1 := by
  rcases Int.units_eq_one_or (χ (Multiplicative.ofAdd (Pi.single i 1))) with h | h
  · left
    rw [signCharTuple, h, map_one]
  · right
    rw [signCharTuple, h]
    exact Units.ext (by simp [intUnitsMap])

theorem rootCharKernel_signCharTuple
    (hk : ringChar k ≠ 2)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) :
    rootCharKernel (signCharTuple (k := k) χ) = kernelRoots χ := by
  ext α
  refine and_congr_right fun _ => ?_
  rw [rootChar_signCharTuple, map_eq_one_iff _ (intUnitsMap_injective hk)]

end Character

section Main

variable (p : ℕ) [Fact p.Prime] {τ : Tag} {k : Type} [Field k] [IsAlgClosed k] [CharP k p]


omit [IsAlgClosed k] in
theorem rootDiagUnit_conj_rootSL2
    (c : Fin τ.rank → kˣ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (z : k) :
    rootDiagUnit τ c * rootSL2 τ k γ (uSL z) * (rootDiagUnit τ c)⁻¹ =
        rootSL2 τ k γ (uSL ((rootChar c γ : k) * z)) ∧
      rootDiagUnit τ c * rootSL2 τ k γ (vSL z) * (rootDiagUnit τ c)⁻¹ =
        rootSL2 τ k γ (vSL ((((rootChar c γ)⁻¹ : kˣ) : k) * z)) := by
  obtain ⟨η, -, hv⟩ := exists_rootSL2_vSL_eq (K := k) hγ
  have hneg : rootChar c (-γ) = (rootChar c γ)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← rootChar_add, neg_add_cancel, rootChar_zero]
  refine ⟨?_, ?_⟩
  · rw [rootSL2_uSL_eq, rootDiagUnit_conj_pinnedX c hγ, rootSL2_uSL_eq, mul_smul_comm]
  · rw [hv, rootDiagUnit_conj_pinnedX c (IsRoot.neg hγ), hv, hneg, mul_left_comm]

omit [IsAlgClosed k] in
theorem finite_setOf_entrywiseFrobGL_eq {n : ℕ} (hn : 1 ≤ n) :
    {g : ModGL τ k | entrywiseFrobGL τ k p n g = g}.Finite := by
  classical
  set P : Polynomial k := Polynomial.X ^ (p ^ n) - Polynomial.X with hPdef
  have hq : 1 < p ^ n := Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
  have hP : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hq
  let φ : ModGL τ k → Label τ → Label τ → k := fun g b l =>
    ((g : Module.End k (RootModule τ k)) (Finsupp.single b 1)) l
  have hφ : Function.Injective φ := fun g g' h =>
    Units.ext (end_ext_single fun b => Finsupp.ext fun l => congrFun (congrFun h b) l)
  have hsub : {g : ModGL τ k | entrywiseFrobGL τ k p n g = g} ⊆
      φ ⁻¹' (Set.univ.pi fun _ => Set.univ.pi fun _ => P.rootSet k) := by
    intro g hg b _ l _
    have h1 := congrArg (fun A : ModGL τ k =>
      ((A : Module.End k (RootModule τ k)) (Finsupp.single b 1)) l) hg
    simp only [Units.coe_map] at h1
    change (entrywise (iterateFrobenius k p n) (g : Module.End k (RootModule τ k))
      (Finsupp.single b 1)) l = _ at h1
    rw [entrywise_single, Finsupp.mapRange_apply, iterateFrobenius_def] at h1
    rw [Polynomial.mem_rootSet]
    refine ⟨hP, ?_⟩
    simp only [hPdef, map_sub, map_pow, Polynomial.aeval_X]
    rw [h1, sub_self]
  exact ((Set.Finite.pi fun _ => Set.Finite.pi fun _ => Polynomial.rootSet_finite P k).preimage
    hφ.injOn).subset hsub


end Main

end CFSG.LieType.AlgebraicGroups
