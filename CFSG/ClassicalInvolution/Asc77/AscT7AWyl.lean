module

public import CFSG.ClassicalInvolution.Asc77.AscT7ASectC

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C21_WylTrans' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' : Subgroup G) (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G),
    Hyp21 p f Ω K K' z u J t W → MuIsoWylD4 Ω W → ∀ H : Subgroup G, rLayer Ω (t * z) ≤ H →
      sigmaGen Ω K ≤ H → ∀ M ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = M

variable {p f}

theorem C21_WylTrans.toWeak (h : C21_WylTrans p f) : C21_WylTrans' p f :=
  fun G _ _ _ Ω K K' z u J t W hh hmu H hD _ => h G Ω K K' z u J t W hh hmu H hD

section Steps


end Steps


section Steps2


end Steps2


end CFSG.ClassicalInvolution.Asc77
