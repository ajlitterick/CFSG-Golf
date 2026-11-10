module

public import CFSG.ClassicalInvolution.Asc77.AscT7FA
public import CFSG.ClassicalInvolution.Asc77.AscIHSectKD
public import CFSG.ClassicalInvolution.Asc77.AscIHSectH

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C21_13_N_ne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      dComp Ω K ≠ dstarComp Ω K →
        Subgroup.centralizer ({t * z} : Set G) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G)

@[expose] def C21_14_N_rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      ¬ (dComp Ω K = dstarComp Ω K ∧ SectionConnected Ω u) →
        Subgroup.centralizer ({u} : Set G) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G)

@[expose] def C21_14_alt_rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ →
        ¬ (dComp Ω K = dstarComp Ω K ∧ SectionConnected Ω u) →
          rLayer Ω u ≤ sigmaGen Ω K ∨
            Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer ({t * z} : Set G)

variable {p f}

theorem c21_13_N_of_ne (hMF : DStarConnectedTwinGen p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) (hC3 : C21_3 p f)
    (h : C21_13_N_ne p f) : C21_13_N p f := by
  intro G _ _ _ Ω K K' z u J t W hh
  by_cases heq : dComp Ω K = dstarComp Ω K
  · exact hh.centralizer_tz_le_normalizer_alpha hMF h3s ⟨hC3, twinNormAlpha_of p f hC3⟩ heq
  · exact h G Ω K K' z u J t W hh heq

theorem c21_14_N_of_rest (hC3 : C21_3 p f) (h : C21_14_N_rest p f) : C21_14_N p f := by
  intro G _ _ _ Ω K K' z u J t W hh
  by_cases hgood : dComp Ω K = dstarComp Ω K ∧ SectionConnected Ω u
  · exact hh.centralizer_u_le_normalizer_alpha ⟨hC3, twinNormAlpha_of p f hC3⟩ hgood.1 hgood.2
  · exact h G Ω K K' z u J t W hh hgood

theorem c21_14_alt_of_rest (h : C21_14_alt_rest p f) : C21_14_alt p f := by
  intro G _ _ _ Ω K K' z u J t W hh hα
  by_cases hgood : dComp Ω K = dstarComp Ω K ∧ SectionConnected Ω u
  · exact Or.inl (hh.rLayer_u_le_sigmaGen hα hgood.1 hgood.2)
  · exact h G Ω K K' z u J t W hh hα hgood


end CFSG.ClassicalInvolution.Asc77
