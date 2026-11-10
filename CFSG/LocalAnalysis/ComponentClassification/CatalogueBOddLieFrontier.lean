module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieAssembly
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieTwistedE6

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOddLie

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup (GeneralizedFitting.subgroup G)]

theorem exceptional_index_two_B_of_odd
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) (t : StatedLieTag)
    (p f : ℕ) (ht : t ∈ chevalleyExceptionalTags) (hp2 : p ≠ 2)
    (hmodel : ChevalleyExceptionalModel (GeneralizedFitting.subgroup G) t p f) :
    CentralTwoBInclusion.Property G := by
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (odd_G2_F4_E8_index_two_B_under_proper_subgroup_B hnonab hindex .G2 (Or.inl rfl) p f
      hp2 hmodel hproper).2
  · exact (odd_G2_F4_E8_index_two_B_under_proper_subgroup_B hnonab hindex .F4
      (Or.inr (Or.inl rfl)) p f hp2 hmodel hproper).2
  · exact odd_E6_E7_twisted_E6_triality_B_frontier hnonab hindex .E6 p f (Or.inl rfl) hp2 hmodel
      hproper
  · exact odd_E6_E7_twisted_E6_triality_B_frontier hnonab hindex .E7 p f (Or.inr (Or.inl rfl))
      hp2 hmodel hproper
  · exact (odd_G2_F4_E8_index_two_B_under_proper_subgroup_B hnonab hindex .E8
      (Or.inr (Or.inr rfl)) p f hp2 hmodel hproper).2
  · exact odd_E6_E7_twisted_E6_triality_B_frontier hnonab hindex .twistedE6 p f
      (Or.inr (Or.inr (Or.inl rfl))) hp2 hmodel hproper
  · exact odd_E6_E7_twisted_E6_triality_B_frontier hnonab hindex .trialityD4 p f
      (Or.inr (Or.inr (Or.inr rfl))) hp2 hmodel hproper


theorem odd_Lie_index_two_B_under_proper_subgroup_B
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2)
    (hodd : OddLieType (GeneralizedFitting.subgroup G))
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) :
    CentralTwoBInclusion.Property G :=
  odd_Lie_index_two_B_of_exceptional hnonab hindex hodd hproper fun t p f ht _ hp2 hex =>
    exceptional_index_two_B_of_odd hnonab hindex hproper t p f ht hp2 hex

end CFSG.ComponentClassification.CatalogueBOddLie
