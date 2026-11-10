module

public import CFSG.ClassicalInvolution.Asc77.AscT7AMain

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C21_YSigma : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → rLayer Ω u ≤ sigmaGen Ω K →
        Subgroup.centralizer ({t * z} : Set G) ≤ sigmaStarNorm Ω K →
          Subgroup.centralizer ({u} : Set G) ≤ sigmaStarNorm Ω K

@[expose] def C21_17_tz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → rLayer Ω (t * z) ≤ sigmaGen Ω K →
        dComp Ω K = dstarComp Ω K →
          Subgroup.centralizer ({t * z} : Set G) ≤ sigmaStarNorm Ω K

@[expose] def C21_E_star : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K →
        (∀ M ∈ dComp Ω K, M ≤ Subgroup.centralizer ({t * z} : Set G)) → MuIsoWylD4 Ω W →
          ∀ M : Subgroup G,
            M ∈ dstarComp Ω K ↔ M ∈ Ω ∧ M ≤ Subgroup.centralizer ({t * z} : Set G)

variable {p f}

section Step14

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}

theorem centralizer_u_le_sigmaStarNorm (h14 : C21_14 p f) (hY : C21_YSigma p f)
    {K K' J W : Subgroup G} {z u t : G} (h : Hyp21 p f Ω K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    (htz : Subgroup.centralizer ({t * z} : Set G) ≤ sigmaStarNorm Ω K) :
    Subgroup.centralizer ({u} : Set G) ≤ sigmaStarNorm Ω K := by
  obtain ⟨-, h14'⟩ := h14 G Ω K K' z u J t W h
  simp only [hα, bot_sup_eq] at h14'
  rcases h14' with h1 | ⟨-, -, h3⟩
  · exact hY G Ω K K' z u J t W h hα h1 htz
  · exact h3.trans htz


end Step14

end CFSG.ClassicalInvolution.Asc77
