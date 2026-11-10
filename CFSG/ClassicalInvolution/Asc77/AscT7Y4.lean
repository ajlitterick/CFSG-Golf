module

public import CFSG.ClassicalInvolution.Asc77.AscT7W13
public import CFSG.ClassicalInvolution.Asc77.AscExactDChain

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)

variable {p f : ℕ} [Fact p.Prime]


variable (p f)

@[expose] def C23_chain5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23Setting p f Ω K K' z →
      Hyp23bData Ω K K' W z u e g →
        (alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ ∧ rLayer Ω e ⊔ rLayer Ω u = ⊤) →
        LayerOrthType p f Ω e 6 (piSign p f) → LayerOrthType p f Ω u 5 true →
          ∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
            (∃ V, LinearBlockStandardPair (GaloisField p f) V (U 0) (U 1)) ∧
            (∃ V, SymplecticBlockPair (GaloisField p f) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤

@[expose] def C23_chain6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23Setting p f Ω K K' z →
      Hyp23bData Ω K K' W z u e g →
        (alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ ∧ rLayer Ω e ⊔ rLayer Ω u = ⊤) →
        LayerOrthType p f Ω e 6 (piSign p f) → LayerOrthType p f Ω u 6 (!piSign p f) →
          ∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
            (∃ V, LinearBlockStandardPair (GaloisField p f) V (U 0) (U 1)) ∧
            (∃ V, TwistedB2BlockPair (minusCoeffs_irr p f) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤

theorem c23_chainX_of_chain56 (h5 : C23_chain5 p f) (h6 : C23_chain6 p f) : C23_chainX p f := by
  intro G _ _ _ Ω K K' W z u e g hs hd hα hE hY
  rcases hY with hY | hY
  · exact Or.inl (h5 G Ω K K' W z u e g hs hd hα hE hY)
  · exact Or.inr (h6 G Ω K K' W z u e g hs hd hα hE hY)


end CFSG.ClassicalInvolution.Asc77
