module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceSix
public import CFSG.LocalAnalysis.StandardType.GGPresentation
public import CFSG.Milestones.CL_LIT_Curtis_Tits_presentation_theorem
public import CFSG.LieType.CurtisTits

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Core

variable {G : Type} [Group G] {U : Type} [Group U]

@[expose] def GGPresentsG0 (G₀ : Subgroup G) (Δ : UniversalRootDatum U) (t : StatedLieTag)
    (n f : ℕ) (ψ : U →* G) : Prop :=
  (StatedLieAdmissible t n 2 f ∧ 2 ≤ Δ.rank) ∧ (ψ.range = G₀ ∧ ψ.ker ≤ Subgroup.center U) ∧
    commutator ↥G₀ = ⊤ ∧ LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f

end Core

section Inputs

@[expose] def GGPropFiveTwentyOneV2Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs →
      (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs) →
        GGScalarsOrWeyl' p B Bs x D J →
          GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) →
      ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
        GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ

@[expose] def GGHypSixV2Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
        GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ →
        Bs ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) →
          ∀ b ∈ Bs, GGPsiInnerDiag (ggU t n f).D ψ b

variable {G : Type} [Group G] [Finite G]


end Inputs

section Presentation

theorem ggPresentsG0_of_presentation {G : Type} [Group G] (t : StatedLieTag) (n f : ℕ)
    (hadm : StatedLieAdmissible t n 2 f) (hrank : 3 ≤ bnRank t n)
    (hrk : 2 ≤ (ggU t n f).D.rank) {ν : GGWeyl (ggU t n f).D →* (ggU t n f).K}
    (hν : GGWeylLift (ggU t n f).D ν) {ι : Type*} {S : ι → Set (Fin (ggU t n f).D.rank → ℤ)}
    (hS : ∀ k, S k ⊆ (ggU t n f).D.roots) (φ : ∀ k, ggSub (ggU t n f).D (S k) →* G)
    {R : Subgroup G} {δ : R →* GGWeyl (ggU t n f).D} (hδ : Function.Surjective δ)
    (hC : GGActsLike (ggU t n f).D S φ ν R δ) (hW : GGWeylInR (ggU t n f).D S φ ν R δ)
    (horb : GGOrbit (ggU t n f).D S)
    (hnt : ∃ k, ∃ γ ∈ S k, ∃ z ∈ (ggU t n f).D.rootGroup γ, ggExt (φ k) z ≠ 1)
    {G₀ : Subgroup G} (hcl : ggClosure (ggU t n f).D S φ R = G₀) :
    ∃ ψ : (ggU t n f).K →* G, GGPresentsG0 G₀ (ggU t n f).D t n f ψ ∧
      ∀ k (x : ggSub (ggU t n f).D (S k)), ψ x = φ k x := by
  subst hcl
  obtain ⟨ψ, hext, -, -, hrange, hker, hq, hmodel⟩ :=
    ggPresentation (CFSG.Milestones.cl_lit_curtis_tits_presentation_theorem.{0} t n 2 f hadm hrank)
        hν hS φ hδ hC hW horb hnt
  exact ⟨ψ, ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, Group.isPerfect_def.mp hq.1, hmodel⟩, hext⟩

end Presentation

section Assembly


end Assembly

end CFSG.StandardType
