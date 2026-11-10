
module

public import CFSG.Quasithin.Background.C1GNBlocks
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.EmptyFaithful.S14111

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Statements

variable {G : Type} [Group G] [Finite G]

@[expose] def C126Statement (C₁ C₂ : Subgroup G → Subgroup G) : Prop :=
  ∀ H T : Subgroup G, IsSQTKTC H → IsSylowTwoOf T H → CharTwo H → IsMinParabolicOf H H →
    C₁ T ≤ centerOf H ∨ H ≤ Subgroup.normalizer (C₂ T : Set G) ∨
      ∃ (r : ℕ) (K : Fin r → Subgroup G), 1 ≤ r ∧
        (∀ i, IsChi0Block H (K i) ∧ ⁅K i, thompsonJ T⁆ = K i) ∧
        (∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥) ∧ twoResidual H = ⨆ i, K i ∧
        (∀ t ∈ T, ∀ i, ∃ j, B6.conjSub t (K i) = K j) ∧
        (∀ i j, ∃ t ∈ T, B6.conjSub t (K i) = K j)


@[expose] def DistinctBlocksCommuteStatement : Prop :=
  ∀ H B₁ B₂ : Subgroup G, CharTwo H → IsBlock2 H B₁ → IsBlock2 H B₂ → B₁ ≠ B₂ → ⁅B₁, B₂⁆ = ⊥


end Statements

end CFSG.Quasithin
