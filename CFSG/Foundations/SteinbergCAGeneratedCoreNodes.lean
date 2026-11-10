module

public import CFSG.Assembly.Defs
public import CFSG.Open.FusionDefs
public import CFSG.Open.UniquenessCaseRankThreeMilestoneDefs
public import CFSG.Open.UniquenessExclusionRankFourMilestoneDefs
public import CFSG.Open.AschbacherProperTwoGeneratedCoreMilestoneDefs
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalizerClosure

public section

namespace CFSG.Foundations.SteinbergCA

theorem pRank_coe_eq_open_pRank {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (Q : Subgroup X) : CFSG.pRank p Q = CFSG.Open.pRank p Q := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
    ← CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top p hp.one_lt]


end CFSG.Foundations.SteinbergCA
