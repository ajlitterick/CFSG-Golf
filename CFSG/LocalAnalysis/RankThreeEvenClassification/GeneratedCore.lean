module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.PrimeSelector
public import CFSG.LocalAnalysis.RankThreeEvenClassification.RankTransport

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] def relativeCentralizer {G : Type u} [Group G] (overgroup subgroup : Subgroup G) :
    Subgroup G := overgroup ⊓ Subgroup.centralizer (subgroup : Set G)

@[expose] def centralizerProduct {G : Type u} [Group G] (overgroup subgroup : Subgroup G) :
    Subgroup G := subgroup ⊔ relativeCentralizer overgroup subgroup


@[expose] noncomputable def aschbacherCore {G : Type u} [Group G] [Finite G]
    (prime threshold : ℕ) (overgroup : Subgroup G) : Subgroup G :=
  ⨆ (subgroup : Subgroup G) (_ : subgroup ≤ overgroup) (_ : threshold ≤ pRank prime subgroup)
    (_ : 3 ≤ pRank prime (centralizerProduct overgroup subgroup)),
    Subgroup.normalizer (subgroup : Set G)

@[expose] def AschCoreLocal (G : Type u) [Group G] [Finite G] (threshold : ℕ) : Prop :=
  ∀ prime ∈ aschbacherPrimes G, ∀ sylow : Sylow prime G,
    ∃ localSubgroup : Subgroup G,
      IsTwoLocal localSubgroup ∧ aschbacherCore prime threshold sylow ≤ localSubgroup


end CFSG.RankThreeEvenClassification.Helpers
