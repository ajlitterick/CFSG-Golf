module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBSharedCore
public import CFSG.CharacterTheory.Semidihedral.StructureTransport
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG CFSG.LocalCores Subgroup
open scoped commutatorElement Pointwise

variable {H : Type*} [Group H]

@[expose] def coreActionKernel (J : Subgroup H) : Subgroup H where
  carrier := {g | g ∈ normalizer (J : Set H) ∧
    ∀ j ∈ J, j⁻¹ * g⁻¹ * j * g ∈ (pPrimeCore 2 J).map J.subtype}
  one_mem' := ⟨one_mem _, fun j _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hgN, hg⟩ ⟨hhN, hh⟩
    refine ⟨mul_mem hgN hhN, fun j hj => ?_⟩
    have hO := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic J (pPrimeCore 2 J)
      (inv_mem hhN)
    have h1 := (mem_normalizer_iff.mp hO _).mp (hg j hj)
    rw [inv_inv] at h1
    rw [show j⁻¹ * (g * h)⁻¹ * j * (g * h) =
      (j⁻¹ * h⁻¹ * j * h) * (h⁻¹ * (j⁻¹ * g⁻¹ * j * g) * h) by group]
    exact mul_mem (hh j hj) h1
  inv_mem' := by
    rintro g ⟨hgN, hg⟩
    refine ⟨inv_mem hgN, fun j hj => ?_⟩
    have h1 := inv_mem (hg _ ((mem_normalizer_iff.mp hgN j).mp hj))
    rwa [show ((g * j * g⁻¹)⁻¹ * g⁻¹ * (g * j * g⁻¹) * g)⁻¹ = j⁻¹ * g⁻¹⁻¹ * j * g⁻¹ by
      group] at h1

theorem mem_coreActionKernel {J : Subgroup H} {g : H} :
    g ∈ coreActionKernel J ↔ g ∈ normalizer (J : Set H) ∧
      ∀ j ∈ J, j⁻¹ * g⁻¹ * j * g ∈ (pPrimeCore 2 J).map J.subtype :=
  Iff.rfl

variable [Finite H]

theorem eq_bot_of_le_two_group_of_le_odd {X P O : Subgroup H} (hP : IsPGroup 2 P)
    (hO : Odd (Nat.card O)) (hXP : X ≤ P) (hXO : X ≤ O) : X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (hP.to_le hXP).exists_card_eq
  have hdvd : Nat.card X ∣ Nat.card O := Subgroup.card_dvd_of_le hXO
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact card_eq_one.mp hk
  · exfalso
    rw [hk] at hdvd
    exact (Nat.not_even_iff_odd.mpr hO)
      (even_iff_two_dvd.mpr ((dvd_pow_self 2 k.succ_ne_zero).trans hdvd))

omit [Finite H] in
theorem pRank_two_le_one_of_card_sylow_le {A : Type*} [Group A] [Finite A]
    (h : ∀ T : Sylow 2 A, Nat.card T ≤ 2) : pRank 2 A ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold pRank
  apply csSup_le'
  rintro r ⟨E, hE, hcard⟩
  obtain ⟨T, hT⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  have h1 : 2 ^ r ≤ Nat.card T := by
    rw [← hcard]
    exact card_le_of_le hT
  have h2 := h T
  by_contra hr
  have h4 : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at h4
  omega


end CFSG.ComponentClassification.UnbalancedLayer
