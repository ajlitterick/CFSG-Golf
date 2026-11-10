module

public import CFSG.ClassicalInvolution.Asc77.AscC25V36
public import CFSG.ClassicalInvolution.Asc77.AscC25V38

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G]


end Basic

section K'

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


end K'

section Defs

variable (p f : ℕ) [Fact p.Prime]


@[expose] def Ident25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 →
      IsFAut R a → IsFAut R' a → z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
        ∀ t' : G, T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' → (∃ g : G, g * z * g⁻¹ = t') →
          (¬ ∃ y : G, y * z * y⁻¹ = t' * z) → a * t' = t' * a →
          ∀ (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
            (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) (n : G),
            n ∈ (S : Subgroup G) → ∀ (hn : n ∈ Subgroup.normalizer (K : Set G))
            (hn' : t' * n * t' ∈ Subgroup.normalizer (K : Set G)),
              diagChar hp hq e ⟨n, hn⟩ = 1 → diagChar hp hq e ⟨t' * n * t', hn'⟩ = 1 →
                (n * a = a * n ∨ n * a = a * n * z)

end Defs

section Proof


end Proof

end CFSG.ClassicalInvolution.Asc77.C25V
