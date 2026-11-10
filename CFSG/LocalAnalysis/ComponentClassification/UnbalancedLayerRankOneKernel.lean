module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerRankOneTwoGroups
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalClassical
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG CFSG.LocalCores Subgroup
open scoped commutatorElement

variable {K : Type*} [Group K] [Finite K]


theorem le_coreActionKernel {J X : Subgroup K} (hJ : IsPComponent 2 J) (hX : IsPComponent 2 X)
    (hXJ : X ≠ J) : X ≤ coreActionKernel J := by
  intro g hg
  obtain ⟨-, hrest⟩ :=
    CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two J X hJ hX
  obtain ⟨hXN, -, hcore, -⟩ := hrest (Ne.symm hXJ)
  refine ⟨hXN hg, fun j hj => ?_⟩
  have hmem : j⁻¹ * g⁻¹ * j * g ∈ ⁅J, X⁆ := by
    rw [show j⁻¹ * g⁻¹ * j * g = ⁅j⁻¹, g⁻¹⁆ by rw [commutatorElement_def, inv_inv, inv_inv]]
    exact commutator_mem_commutator (inv_mem hj) (inv_mem hg)
  exact (mem_inf.mp (hcore hmem)).1

omit [Finite K] in
theorem mem_normalizer_iff_conjugate_eq {J : Subgroup K} {g : K} :
    g ∈ normalizer (J : Set K) ↔ conjugate J g = J := by
  constructor
  · exact conjugate_eq_of_mem_normalizer
  · intro h
    rw [mem_normalizer_iff]
    intro x
    rw [← mem_conjugate_iff, h]


omit [Finite K] in
theorem mem_normalizer_inf {A B : Subgroup K} {g : K} (hA : g ∈ normalizer (A : Set K))
    (hB : g ∈ normalizer (B : Set K)) : g ∈ normalizer ((A ⊓ B : Subgroup K) : Set K) := by
  rw [mem_normalizer_iff]
  intro x
  rw [mem_inf, mem_inf]
  exact and_congr (mem_normalizer_iff.mp hA x) (mem_normalizer_iff.mp hB x)


end CFSG.ComponentClassification.UnbalancedLayer
