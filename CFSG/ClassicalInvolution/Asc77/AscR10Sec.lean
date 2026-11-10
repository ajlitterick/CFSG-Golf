module

public import CFSG.ClassicalInvolution.Asc77.AscR10Mod
public import CFSG.ClassicalInvolution.RouteD.G2D4T3D4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.R10

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.G2D4Models
  CFSG.Assembly.LowTwoRank

variable {Y : Type} [Group Y] [Finite Y] {p f n : ℕ} [Fact p.Prime]


theorem exists_g2_component (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hIH : CITBelowU p f n)
    (hlt : Nat.card Y < n) {Λ : Set (Subgroup Y)} (hΛ : HypOmegaMod p f Λ)
    {K J : Subgroup Y} {zK zJ : Y} (hK : K ∈ Λ) (hv : AViol Λ K J zK zJ) :
    ∃ (D : OmegaLie p f (oddQuotientFamily Λ)) (i : Fin D.card)
      (R : Subgroup (D.model i).K), D.tag i = .G2 ∧ R ∈ D.cls i ∧
        K.map (oddQuot Y) = R.map (D.hom i) := by
  obtain ⟨a, hQ⟩ := quotViol_of_aViol hp2 hq hΛ hK hv
  have hΦ : HypOmegaMod p f (oddQuotientFamily Λ) :=
    oddQuotHyp p f hp2 hq Y Λ hΛ (classicalInvolutionOddCore Y)
      (CFSG.ComponentClassification.OddCore.odd_card Y)
  have hO : classicalInvolutionOddCore (Y ⧸ classicalInvolutionOddCore Y) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree Y
  have hlt' : Nat.card (Y ⧸ classicalInvolutionOddCore Y) < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)) hlt
  obtain ⟨D⟩ := ih8_exists_omegaLie hIH hΦ.conjInvariant hΦ.classical
    ⟨_, mem_oddQuotientFamily hK⟩ hO hlt'
  obtain ⟨i, R, S, hR, hS, hKR, hJS⟩ := hQ.exists_components D
  refine ⟨D, i, R, ?_, hR, hKR⟩
  by_contra hi
  rw [hKR, hJS] at hQ
  by_cases hD : D.tag i = .trialityD4
  · exact quotViol_false_of_trialityD4 hp2 hq hΦ D hD hR hS hQ
  · exact hQ.false_of_classical hp2 hq hΦ D hi hD hR hS


end CFSG.ClassicalInvolution.Asc77.R10
