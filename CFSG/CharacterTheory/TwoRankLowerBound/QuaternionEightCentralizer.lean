module

public import CFSG.CharacterTheory.TwoRankLowerBound.RootProjection
public import CFSG.CharacterTheory.TwoRankLowerBound.QuaternionEightFusion

public section

open scoped Classical Pointwise

namespace CFSG.TwoRankLowerBound.Helpers

theorem two_element_isConj_sylow {G : Type*} [Group G] [Finite G]
    (sylow : Sylow 2 G) (element : G) (horder : ∃ exponent, orderOf element = 2 ^ exponent) :
    ∃ member : (sylow : Subgroup G), IsConj element (member : G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpgroup : IsPGroup 2 (Subgroup.zpowers element) := by
    obtain ⟨exponent, hexponent⟩ := horder
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hexponent])
  obtain ⟨otherSylow, hle⟩ := hpgroup.exists_le_sylow
  obtain ⟨conjugator, hconjugator⟩ := MulAction.exists_smul_eq G otherSylow sylow
  have hmember : conjugator * element * conjugator⁻¹ ∈ (sylow : Subgroup G) := by
    rw [← hconjugator]
    change conjugator * element * conjugator⁻¹ ∈ ((conjugator • otherSylow : Sylow 2 G) : Set G)
    rw [Sylow.coe_smul]
    exact ⟨element, hle (Subgroup.mem_zpowers element), rfl⟩
  exact ⟨⟨_, hmember⟩, isConj_iff.mpr ⟨conjugator, rfl⟩⟩


end CFSG.TwoRankLowerBound.Helpers
