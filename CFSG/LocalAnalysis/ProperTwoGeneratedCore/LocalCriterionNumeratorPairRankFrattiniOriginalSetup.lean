module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniAmbient
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum
import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini

open CFSG CFSG.ShultStronglyClosedTI LocalCriterionGeometry LocalCriterionFourGroupCommutator
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G]


theorem centralizer_four_group_commutes (W : Subgroup G) (t : G)
    (hWt : W ≤ Subgroup.centralizer ({t} : Set G)) (w : W) : Commute (w : G) t :=
  Subgroup.mem_centralizer_singleton_iff.mp (hWt w.property)

theorem original_pair_flip_order [Finite G] {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    orderOf t = 2 :=
  order_two_of_mem_pointClass h.local_datum.distinguished_order ht.1


end CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini
