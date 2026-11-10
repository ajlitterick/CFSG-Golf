module

public import CFSG.LocalAnalysis.StandardType.GGWeylSimpleSystemsConj
public import CFSG.LocalAnalysis.StandardType.GGResLeviDatumSides
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeSides

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResLeviDatum_of_sides_conj {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs L J K : Subgroup G} (hL : GGResSideDatum p Bs L J)
    (hK : GGResSideDatum p Bs K J) : GGResLeviDatum p Bs L J K ggSelAny ggTypAny :=
  ggResLeviDatum_of_sides ggWeylSimpleSystemsConjInput_holds hp2 hL hK


end CFSG.StandardType
