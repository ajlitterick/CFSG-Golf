module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Component3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def InducesOuterOn {X : Type} [Group X] (a : X) (L : Subgroup X) : Prop :=
  a ∈ Subgroup.normalizer (L : Set X) ∧ ¬ ∃ y ∈ L, ∀ w ∈ L, a * w * a⁻¹ = y * w * y⁻¹

@[expose] def IsFieldOmegaA (p : ℕ) (M H R : Subgroup G)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) (E : Subgroup G) : Prop :=
  E ≤ R ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
    (E.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ L ≠ ⊥ ∧
    ∃ a ∈ (E.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)),
      InducesOuterOn a L


end CFSG.LocalAnalysis.RankThreeTheoremC
