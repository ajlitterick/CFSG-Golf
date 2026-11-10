module

public import CFSG.LocalAnalysis.StandardType.GGHypSixAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

@[expose] def GGInnerDiagMpInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU t n f).K → ∀ G₀ : Subgroup G, ψ.range = G₀ →
    ∀ P : LargeEvenMarkProp ↥G₀, LargeEvenMarking ↥G₀ P →
      LargeEvenMarking ↥G₀ (fun lab R _ I F θ => P lab R I F θ ∧
        ∀ c ∈ Subgroup.normalizer (G₀ : Set G),
          (∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ) →
            GGPsiInnerDiag (ggU t n f).D ψ c)


variable {G : Type} [Group G] [Finite G]

theorem ggTorusOnRoot_of_innerDiagOn_mp (hMp : GGInnerDiagMpInput) {U : Type*} [Group U]
    {Δ : UniversalRootDatum U} {ψ : U →* G} {Bs K : Subgroup G} (hK : GGInnerDiagOn Bs K)
    (hcomp : GGCompatPresented Δ ψ K) (hKle : K ≤ ψ.range) :
    ∃ γ ∈ Δ.roots, ∃ u : U, ∀ b ∈ Bs, GGTorusOnRoot Δ ψ b γ u := by
  obtain ⟨t', n', f', ψ', hadm', hrk', hker', hrange', δ, hδ, γ, hγ, u, hm⟩ := hcomp
  obtain ⟨-, lab, -, hraw⟩ := hMp G t' n' f' ψ' hadm' hrk' hker' K hrange' _ hK
  obtain ⟨R, _, I, F, -, -, θ, ⟨hBsN, hI⟩, himp⟩ := largeEvenRawDatum_exists hraw
  refine ⟨γ, hγ, u, fun b hb => ?_⟩
  exact ggTorusOnRoot_of_rootMatch (hrange' ▸ hKle) hδ hm (himp b (hBsN hb) (hI b hb))


end CFSG.StandardType
