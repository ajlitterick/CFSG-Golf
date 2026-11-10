module

public import CFSG.ClassicalInvolution.Balance.BootstrapStage2Alpha
public import CFSG.ClassicalInvolution.Balance.LayerGenerationLie

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem componentLayersAt_of_model [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h27 : p ^ f ≠ 27) (h0 : ModelClauseZero)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) {A : Subgroup G}
    (hA2 : ∀ x ∈ A, x * x = 1) (hmodel : LayerGenerationModel) :
    ∀ a ∈ A, a ≠ 1 → ComponentLayersAt Ω A a := fun a ha ha1 =>
  componentLayersAt_of_layerGenerationOn (P := fun L => IsOddLieComponentBig L)
    (fun _ hL => omegaFreeAt_or_rankOneAt_or_isOddLieComponentBig hp2 h0 fundamentalWholeA1 hq hΩ
      hIH (not_subset_center_of_ne_one hnab ha1) (NoComponentOverF3.of_ne_27 a hq h27) hL)
    (LayerGenerationLieBig.of_model hA2 hmodel ha)


end CFSG.ClassicalInvolution.Balance.Bootstrap
