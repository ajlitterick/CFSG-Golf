module

public import CFSG.LocalAnalysis.LargeEvenClassification.NormalEightFourExtension
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsSectionBounds

public section

namespace CFSG.LargeEvenClassification.Helpers

open CFSG.Open

universe u

theorem isolated_four_normal_elementary_card_lt_eight
    {S : Type u} [Group S] [Finite S] (htwo : IsPGroup 2 S)
    (V : Subgroup S) (hV : IsElemAbelian 2 V) (hVcard : Nat.card V = 4)
    (hcentralizer : twoRank (Subgroup.centralizer (V : Set S)) = 2)
    (A : Subgroup S) (hAnormal : A.Normal) (hA : IsElemAbelian 2 A) :
    Nat.card A < 8 := by
  by_contra hlarge
  let : A.Normal := hAnormal
  have hbound := normal_elementary_rank_three_four_centralizer htwo A hA
    (by omega) V hV hVcard
  rw [hcentralizer] at hbound
  omega

theorem isolated_four_no_normal_eight
    {S : Type u} [Group S] [Finite S] (htwo : IsPGroup 2 S)
    (V : Subgroup S) (hV : IsElemAbelian 2 V) (hVcard : Nat.card V = 4)
    (hcentralizer : twoRank (Subgroup.centralizer (V : Set S)) = 2) :
    ∀ A : Subgroup S, A.Normal → IsElemAbelian 2 A → Nat.card A ≠ 8 := by
  intro A hAnormal hA
  exact (isolated_four_normal_elementary_card_lt_eight htwo V hV hVcard
    hcentralizer A hAnormal hA).ne

theorem isolated_four_four_generators
    {S : Type u} [Group S] [Finite S] (htwo : IsPGroup 2 S)
    (V : Subgroup S) (hV : IsElemAbelian 2 V) (hVcard : Nat.card V = 4)
    (hcentralizer : twoRank (Subgroup.centralizer (V : Set S)) = 2)
    (U : Subgroup S) :
    ∃ X : Finset S, X.card ≤ 4 ∧ Subgroup.closure (X : Set S) = U := by
  exact macwilliams_four_generators htwo
    (isolated_four_no_normal_eight htwo V hV hVcard hcentralizer) U


end CFSG.LargeEvenClassification.Helpers
