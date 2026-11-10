module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandFourteen

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Notation

variable {G : Type} [Group G]

abbrev GGRCSNbar (r : G) : Type :=
  ↥(Subgroup.centralizer ({r} : Set G)) ⧸
    CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G))

noncomputable abbrev ggRCSImg (r : G) (Y : Subgroup G) : Subgroup (GGRCSNbar r) :=
  (Y.subgroupOf (Subgroup.centralizer ({r} : Set G))).map
    (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G))))

end Notation

section Inputs

@[expose] def GGRootCentSummandStructInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        ∃ 𝒮 : Set (Subgroup (GGRCSNbar r)),
          (∀ S ∈ 𝒮, GGRCSQuasiPiece p (ggRCSImg r (ggM p B x L D J)) S ∨
            (p = 3 ∧ GGRCSSThreePiece (ggRCSImg r (ggM p B x L D J)) S)) ∧
          ∀ y : ↥(Subgroup.centralizer {r}),
            (y : G) ∈ ggOTwoPrime (ggG0 p B x L D J ⊓ Subgroup.centralizer {r}) →
              (y : G) ^ p = 1 → QuotientGroup.mk' _ y ∈ sSup 𝒮


@[expose] def GGRootCentAutKNotExcInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        ∀ K S : Subgroup (GGRCSNbar r),
          GGRCSAutKSetting p (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K S →
            GGRCSAutKNotExc p (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K


end Inputs

end CFSG.StandardType
