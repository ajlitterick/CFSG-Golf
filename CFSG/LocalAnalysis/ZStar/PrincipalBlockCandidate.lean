module

public import CFSG.LocalAnalysis.ZStar.Helpers

public section

namespace CFSG

namespace ZStar

open ZStar.Helpers

abbrev A (G : Type*) [Group G] := GroupAlgebraTwo G

theorem principalBlockCandidate_mul_eq_self_of_augmentation_one
    (G : Type*) [Group G] [Fintype G]
    (f : A G) (hfcentral : IsGroupCentral G f)
    (hfidempotent : f * f = f) (hfaugmentation : augmentationHom G f = 1) :
    principalBlockCandidate G * f = principalBlockCandidate G := by
  have hcomplement : IsAugmentationZeroCentralIdempotent G (1 - f) := by
    refine ⟨hfcentral.one_sub G, one_sub_idempotent hfidempotent, ?_⟩
    rw [map_sub, map_one, hfaugmentation, sub_self]
  have hannihilates := principalBlockCandidate_annihilates G (1 - f) hcomplement
  rw [mul_sub, mul_one] at hannihilates
  exact (sub_eq_zero.mp hannihilates).symm


end ZStar

end CFSG
