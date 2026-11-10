module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceBridge

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Marked

variable {G : Type} [Group G] [Finite G]


end Marked


section Closing


end Closing

section Genuine

@[expose] def GGSixHypV2I1 {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) : Prop :=
  GGSixHypV2 p B Bs x L D J ∧ Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D

@[expose] def GGSecOneFiveV2I1Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → IsCharTwoType G → 4 ≤ evenRank G → ∀ p : ℕ, p ∈ LargeEvenBeta 4 G →
    ∀ (B : Subgroup G) (x : G) (L : Subgroup G), LargeEvenSStar p B x L →
      LargeEvenStandardType p B x L → ∃ Bs D J : Subgroup G, GGSixHypV2I1 p B Bs x L D J

@[expose] def GGSecSixV2I1Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → IsCharTwoType G → 4 ≤ evenRank G → ∀ p : ℕ, p ∈ LargeEvenBeta 4 G →
    ∀ (B : Subgroup G) (x : G) (L : Subgroup G), LargeEvenSStar p B x L →
      LargeEvenStandardType p B x L → ∀ Bs D J : Subgroup G,
      ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
        GGSixHypV2Core p B Bs x L D J (ggU t n f).D t n f ψ →
        Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
        Subgroup.normalizer (ggG0 p B x L D J : Set G) = ⊤ ∨
          GGHoltAt (Subgroup.normalizer (ggG0 p B x L D J : Set G))


end Genuine

section Skeleton


end Skeleton

end CFSG.StandardType
