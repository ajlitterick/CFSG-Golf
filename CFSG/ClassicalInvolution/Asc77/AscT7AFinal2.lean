module

public import CFSG.ClassicalInvolution.Asc77.AscT7AWeak

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C21_13_star : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K →
        dComp Ω K ≠ dstarComp Ω K

variable {p f}

theorem C21_13_wyl_of_star (h12 : C21_12 p f) (h : C21_13_star p f) : C21_13_wyl p f := by
  intro G _ _ _ Ω K K' z u J t W hh hα hD
  rcases h12 G Ω K K' z u J t W hh with heq | hmu
  · exact absurd heq (h G Ω K K' z u J t W hh hα hD)
  · exact hmu


end CFSG.ClassicalInvolution.Asc77
