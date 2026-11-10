module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionFrame
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwo

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix

@[expose] def GGLinearSemisimpleComponentInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m f : ℕ)
    (ψ : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G),
    ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) →
    ∀ (P : GL (Fin (m + 1)) (GaloisField 2 f)) (d : Fin (m + 1) → (GaloisField 2 f)ˣ) (b : G),
      (b, LinFusion.ggFrameDiag P d) ∈ LinFusion.ggInducedPairs ψ →
      ∀ L₁ : Subgroup G, IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {b}) →
        ∃ I : Finset (Fin (m + 1)), L₁ = LinFusion.ggFrameBlock (GaloisField 2 f) ψ P I ∧
          ∀ i ∈ I, ∀ j ∈ I, d i = d j

section Inputs


end Inputs

end CFSG.StandardType
