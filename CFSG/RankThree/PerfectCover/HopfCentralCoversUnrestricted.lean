module

public import CFSG.RankThree.PerfectCover.HopfCentralCovers
import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite

public section

namespace CFSG.RankThree.PerfectCover

open Subgroup

universe u v

theorem finite_of_quasisimple_finite_central_quotient {L : Type u} {X : Type v} [Group L]
    [Group X] [Finite X] (hL : CFSG.IsQuasisimple L) (e : L ⧸ center L ≃* X) : Finite L := by
  have : Group.IsPerfect L := hL.1
  have : Finite (HopfCover X) := finite_hopfCover (isPerfect_of_quasisimple_quotient hL e)
  have hk : (centralQuotientMap e).ker ≤ center L := (centralQuotientMap_ker e).le
  exact Finite.of_surjective (hopfLift (centralQuotientMap e) (centralQuotientMap_surjective e) hk)
    (hopfLift_surjective (centralQuotientMap e) (centralQuotientMap_surjective e) hk)


end CFSG.RankThree.PerfectCover
