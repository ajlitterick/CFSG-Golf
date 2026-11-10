module

public import CFSG.ClassicalInvolution.Q3.TL3S8BCount
public import CFSG.ClassicalInvolution.Q3.TL3S8BCore

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def TightThm6SylowBelow (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IH (Nat.card G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G), TightDatum R S t → TightFStarOK G t →
      Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2) → ∀ T : Subgroup G,
      IsSylow2Of T
        (Subgroup.normalizer (((S : Subgroup R).map R.subtype : Subgroup G) : Set G)) →
      IsSylow2Of T ⊤ → Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R)) →
        TwoSubgroupsFourGenerated (genFittingFStar G)

theorem TightThm6SylowBelow.mono {IH IH' : ℕ → Prop} (h : ∀ n, IH' n → IH n)
    (hI : TightThm6SylowBelow IH) : TightThm6SylowBelow IH' :=
  fun G _ _ hb => hI G (h _ hb)


end CFSG.ClassicalInvolution.Q3
