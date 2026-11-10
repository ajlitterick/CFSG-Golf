module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalizedIntersectionCorrector
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerFlips
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointTransport

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI
open LocalCriterionGeometry LocalCriterionInvariantNormalizer
open LocalCriterionDoubleTransitiveNormalizer LocalCriterionNormalizedIntersection

universe u

variable {G : Type u} [Group G] [Finite G]

theorem local_involution_point_normalized_intersection_sylow_flips
    (H : Subgroup G) (z : G) (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (X : Subgroup G)
    (hX : Subgroup.closure ((pairPointStabilizer H beta : Set G) ∪ {t}) ≤
      Subgroup.normalizer (X : Set G)) :
    ∀ p : ℕ, p.Prime →
      ∀ Q : Sylow p (X ⊓ triplePointStabilizer H z beta : Subgroup G),
        (conjugacyWithin (pairPointStabilizer H beta) t ∩
          (Subgroup.normalizer
            (((Q : Subgroup (X ⊓ triplePointStabilizer H z beta : Subgroup G)).map
              (X ⊓ triplePointStabilizer H z beta).subtype : Subgroup G) : Set G) :
            Set G)).Nonempty := by
  have hpairX : pairFlipGroup H beta t ≤ Subgroup.normalizer (X : Set G) := by
    rw [pairFlipGroup_eq_generated]
    exact hX
  intro p hp Q
  have hzbot : z ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]
  obtain ⟨_, P₀, _, hzP₀, _⟩ :=
    ((local_involution_point_three_point_sylow_criterion h S hzS hzcenter beta hbeta).2
      p hp).1 (⊥ : Subgroup G) bot_le IsPGroup.of_bot hzbot
  obtain ⟨s₀, hs₀, hs₀norm⟩ :=
    original_triple_sylow_normalizer_supplied_flip_class_intersection
      h S hzS hzcenter hdoubly beta hbeta p hp P₀ hzP₀ t ht
  exact normalized_intersection_sylow_corrector H beta t
    (triplePointStabilizer H z beta) X
    (show triplePointStabilizer H z beta ≤ pairPointStabilizer H beta from inf_le_left)
    hpairX p hp P₀ s₀ hs₀ hs₀norm Q


end CFSG.ProperTwoGeneratedCore
