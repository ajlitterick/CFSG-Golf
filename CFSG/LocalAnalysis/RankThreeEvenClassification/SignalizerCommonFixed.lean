module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerSubgroups

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u


@[expose] noncomputable def signalizerCommonFixed {G : Type u} [Group G]
    (subactor : Subgroup G) (signalizer : G → Subgroup G) : Subgroup G :=
  ⨅ (element : G) (_ : element ∈ subactor) (_ : element ≠ 1), signalizer element

theorem signalizerCommonFixed_le_value {G : Type u} [Group G]
    (subactor : Subgroup G) (signalizer : G → Subgroup G)
    (element : G) (hmem : element ∈ subactor) (hne : element ≠ 1) :
    signalizerCommonFixed subactor signalizer ≤ signalizer element := by
  exact iInf_le_of_le element (iInf_le_of_le hmem (iInf_le_of_le hne le_rfl))

theorem signalizerCommonFixed_le_centralizer {G : Type u} [Group G]
    (prime : ℕ) (actor subactor : Subgroup G) (signalizer : G → Subgroup G)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer) (hle : subactor ≤ actor) :
    signalizerCommonFixed subactor signalizer ≤ Subgroup.centralizer (subactor : Set G) := by
  intro element helement
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  by_cases hne : member = 1
  · rw [hne, one_mul, mul_one]
  · exact (Subgroup.mem_centralizer_singleton_iff.mp
      (hsignalizer.le_centralizer member (hle hmember) hne
        (signalizerCommonFixed_le_value subactor signalizer member hmember hne helement))).symm

theorem signalizerCommonFixed_eq_value_centralizer {G : Type u} [Group G]
    (prime : ℕ) (actor subactor : Subgroup G) (signalizer : G → Subgroup G)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer) (hle : subactor ≤ actor)
    (element : G) (hmem : element ∈ subactor) (hne : element ≠ 1) :
    signalizerCommonFixed subactor signalizer =
      signalizer element ⊓ Subgroup.centralizer (subactor : Set G) := by
  apply le_antisymm
  · exact le_inf (signalizerCommonFixed_le_value subactor signalizer element hmem hne)
      (signalizerCommonFixed_le_centralizer prime actor subactor signalizer hsignalizer hle)
  · apply le_iInf
    intro member
    apply le_iInf
    intro hmember
    apply le_iInf
    intro hmemberNe
    exact (inf_le_inf le_rfl
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hmember))).trans
      (hsignalizer.balance element (hle hmem) hne member (hle hmember) hmemberNe)


end CFSG.RankThreeEvenClassification.Helpers
