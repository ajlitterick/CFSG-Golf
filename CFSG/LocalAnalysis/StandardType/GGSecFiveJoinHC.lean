module

public import CFSG.LocalAnalysis.StandardType.GGCentralQuotientEq
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatRestWOfIdent
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinHCDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section JoinHC

variable {G : Type} [Group G] [Finite G]

theorem ggJoin_le_ggG0 {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (h𝒦 : GGNbrSet p B x D J 𝒦) :
    L ⊔ ⨆ K ∈ 𝒦, K ≤ ggG0 p B x L D J := by
  refine sup_le (le_ggG0_left p B x L D J) ?_
  refine iSup₂_le ?_
  intro K hK
  obtain ⟨y, hy⟩ := h𝒦.2 K hK
  exact le_ggG0_of_ggNbr hy


end JoinHC

end CFSG.StandardType

end
