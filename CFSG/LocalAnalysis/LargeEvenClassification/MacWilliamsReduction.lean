module

public import CFSG.LocalAnalysis.LargeEvenClassification.AbelianNormalRank
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallAbelianModels
public import CFSG.LocalAnalysis.LargeEvenClassification.NormalFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.AbelianCoordinates

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem exists_maximal_abelian_normal {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] : ∃ Normal : Subgroup Ambient, Normal.Normal ∧ IsMulCommutative Normal ∧
      ∀ Larger : Subgroup Ambient,
        Larger.Normal → IsMulCommutative Larger → Normal ≤ Larger → Larger ≤ Normal := by
  have hbottom : (⊥ : Subgroup Ambient).Normal ∧ IsMulCommutative (⊥ : Subgroup Ambient) :=
    ⟨inferInstance, inferInstance⟩
  obtain ⟨Normal, _, hmaximal⟩ := Finite.exists_le_maximal
    (p := fun Normal : Subgroup Ambient => Normal.Normal ∧ IsMulCommutative Normal) hbottom
  refine ⟨Normal, hmaximal.1.1, hmaximal.1.2, ?_⟩
  intro Larger hnormal hcommutative hle
  exact hmaximal.2 ⟨hnormal, hcommutative⟩ hle

theorem small_rank_two_selfCentralizing_four_generators {Ambient : Type groupUniverse}
    [Group Ambient] [Finite Ambient] (hpgroup : IsPGroup 2 Ambient)
    (Normal : Subgroup Ambient) [Normal.Normal] {upper lower : ℕ}
    (hlower : 0 < lower) (hordered : lower ≤ upper) (hsmall : upper + lower ≤ 3)
    (coordinates : Normal ≃* Multiplicative (ZMod (2 ^ upper)) ×
      Multiplicative (ZMod (2 ^ lower)))
    (hselfCentralizing : Subgroup.centralizer (Normal : Set Ambient) = Normal)
    (SubgroupOfAmbient : Subgroup Ambient) :
    ∃ generators : Finset SubgroupOfAmbient,
      Subgroup.closure (generators : Set SubgroupOfAmbient) = ⊤ ∧ generators.card ≤ 4 := by
  have hcases : (upper = 1 ∧ lower = 1) ∨ (upper = 2 ∧ lower = 1) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hcommutative : IsMulCommutative Normal := by
      apply isMulCommutative_iff.mpr
      intro first second
      apply coordinates.injective
      rw [map_mul, map_mul, mul_comm]
    have hcard : Nat.card Normal = 4 := by
      rw [Nat.card_congr coordinates.toEquiv, Nat.card_eq_fintype_card]
      decide
    obtain ⟨generators, hgenerates, hcardBound⟩ := abelian_normal_four_three_generators hpgroup Normal
      hcommutative hcard hselfCentralizing SubgroupOfAmbient
    exact ⟨generators, hgenerates, hcardBound.trans (by decide)⟩
  · exact fourTwo_selfCentralizing_four_generators hpgroup Normal coordinates
      hselfCentralizing SubgroupOfAmbient


end CFSG.LargeEvenClassification.Helpers
