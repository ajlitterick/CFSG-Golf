module

public import CFSG.LocalAnalysis.ZStar.PrincipalBlockCandidate
public import CFSG.LocalAnalysis.ZStar.BrauerProjection

public section

namespace CFSG

namespace ZStar.BrauerPrincipal

open ZStar.Helpers ZStar
  ZStar.BrauerProjection

universe u

variable {G : Type u} [Group G] [Fintype G]

noncomputable local instance subgroupFintype (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

abbrev involutionCentralizer (w : G) : Subgroup G :=
  Subgroup.centralizer ({w} : Set G)

@[expose] noncomputable def projectedPrincipalBlock (w : G) :
    GroupAlgebraTwo (involutionCentralizer w) :=
  brauerProjection w (principalBlockCandidate G)


end ZStar.BrauerPrincipal

end CFSG
