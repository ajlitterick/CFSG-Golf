module

public import CFSG.RankThree.GF2n.Smith81.Sec1Main
public import CFSG.RankThree.GF2n.Smith81.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

section Consequences

variable [Finite G] {M Q Z B : Subgroup G} {z v : G}

theorem centralizer_le_M (Hs : StrothHyp M Q Z) {a : G} (ha : a ∈ Z) (ha1 : a ≠ 1) :
    Subgroup.centralizer ({a} : Set G) ≤ M := by
  intro c hc
  have h := IsZConjugate.mem_normalizer_of_commute Hs (IsZConjugate.self Z) ha1 ha
    (show Commute c a from Subgroup.mem_centralizer_singleton_iff.mp hc)
  rwa [Hs.normalizer_Z.1] at h


end Consequences

end CFSG.RankThree.GF2n.Smith81
