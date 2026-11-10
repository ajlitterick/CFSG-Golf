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


@[expose] def GGPseudoReflStabInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J →
      ∀ φ ∈ ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs, GGIsPseudoReflection p φ →
        φ ∈ ggAutomizer (ggG0 p B x L D J) Bs


section Proof


end Proof


end CFSG.StandardType
