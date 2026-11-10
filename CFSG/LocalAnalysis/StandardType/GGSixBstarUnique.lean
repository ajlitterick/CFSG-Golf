module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueBasic
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Ctx

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}


theorem GGSixCtxV2.bstarUnique_of_noOffender (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (hNO : GGNoOffender p (ggM p B x L D J) Bs) : GGSixBstarUnique p B Bs x L D J :=
  fun _ hPM hPp hBsP _ _ hEP hE =>
    unique_of_noOffender h.prime h.bstar.2.1 h.bstar.2.2.2 hNO hPM hPp hBsP hEP hE


end Ctx

section Inputs

@[expose] def GGSixBstarNoOffenderInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ → GGNoOffender p (ggM p B x L D J) Bs

theorem ggSixBstarUniqueV2Input_of_noOffender (h : GGSixBstarNoOffenderInput) :
    GGSixBstarUniqueV2Input :=
  fun G _ _ p B Bs x L D J t n f ψ hctx hC =>
    hctx.bstarUnique_of_noOffender (h G p B Bs x L D J t n f ψ hctx hC)


end Inputs

end CFSG.StandardType
