module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOmega
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGCorFiveTwentyHyp (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) :
    Prop :=
  GGConfig p B Bs x L D J ∧ GGOpAutTrivial p Bs ∧ GGInnerDiagAll p B Bs x L D J ∧
    GGNoTransvection p Bs ∧ GGInnerDiagOn Bs (ggG0 p B x L D J)

end Defs


section Proof


end Proof


end CFSG.StandardType
