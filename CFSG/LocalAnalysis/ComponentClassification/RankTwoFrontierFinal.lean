module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFrontierLeaves
import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuH1Final
import CFSG.Sporadic.SuzRecog.MixedCell
import CFSG.Sporadic.SuzRecog.SuzLeaf
import CFSG.Sporadic.J2
import CFSG.Sporadic.Suz.Simple
import CFSG.Sporadic.He.Simple
import CFSG.Sporadic.Ru
import CFSG.Sporadic.Co1

public section

namespace CFSG.ComponentClassification.RankTwoStandard

open CFSG.Blueprint


theorem ct_rank_two_standard_recognition_models
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Assembly.KProper Catalog G) (L : Subgroup G) (hL : Open.standardComponentIsStandard L)
    (hrank : 2 ≤ Open.pRank 2 (Subgroup.centralizer (L : Set G))) :
    (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
      (NativeSporadic.IsSporadic G .J2 ∨ NativeSporadic.IsSporadic G .Suz ∨
        NativeSporadic.IsSporadic G .He ∨ NativeSporadic.IsSporadic G .Ru ∨
        NativeSporadic.IsSporadic G .Co1) :=
  ct_rank_two_standard_recognition_of_leaves GMS78.ruH1Stmt
      Sporadic.SuzRecog.MixedCell.mixedCellDichotomy G
    hnonab hK L hL hrank


end CFSG.ComponentClassification.RankTwoStandard
