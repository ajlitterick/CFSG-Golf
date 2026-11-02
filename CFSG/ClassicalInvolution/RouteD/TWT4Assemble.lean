module

public import CFSG.ClassicalInvolution.RouteD.TWT4Fus
public import CFSG.ClassicalInvolution.RouteD.TWZSu4Odd

public section

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.RouteD.NonClassical CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.RouteD.TWZ
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.RouteD.TWT4

section Assemble

variable {p f : ℕ} [Fact p.Prime]

theorem ne_two_of_mod_four_eq_three (hmod : (p ^ f) % 4 = 3) : p ≠ 2 := by
  rintro rfl
  rcases f with _ | _ | f
  · simp at hmod
  · simp at hmod
  · rw [pow_succ, pow_succ] at hmod
    omega

theorem twinYRankOn_psu4_of_p1' (hmod : (p ^ f) % 4 = 3)
    (hY1 : TwinYP1On p f fun t n => t = .PSU ∧ n = 4) :
    TwinYRankOn p f fun t n => t = .PSU ∧ n = 4 := by
  by_cases h5 : 5 ≤ p ^ f
  · exact twinYRankOn_psu4_of_p1 (ne_two_of_mod_four_eq_three hmod) h5 hmod hY1
  · intro G _ _ _ hnab K z S
    exact absurd S.five h5

theorem twinSU4Three_of_fusion (hΩall : HypOmegaModAll p f) (hAE : AEmptyTwinExact p f)
    (hcls : TwinInvolution p f) (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f)
    (hF : TwinSU4Fusion p f) : TwinSU4Three p f := by
  intro hmod
  have hp2 : p ≠ 2 := ne_two_of_mod_four_eq_three hmod
  have hV := twinYVisibleOn_of_fusion hF hmod
  have hNC := twinYNoCentralOn_of_fusion hF hmod
  have hPL : ∀ t n, (t = .PSU ∧ n = 4) → ListedTwin t n := fun t n h =>
    Or.inr (Or.inr (Or.inl h))
  have hGen : TwinYGenTOn p f fun t n => t = .PSU ∧ n = 4 := by
    by_cases h5 : 5 ≤ p ^ f
    · exact twinYGenTOn_of_model fun t n _ hP => by
        obtain ⟨rfl, rfl⟩ := hP
        exact twinMFGeneration_psu4 hp2 h5
    · intro G _ _ _ hnab K z S
      exact absurd S.five h5
  have hP1 := TWS.twinYP1On_of_visible_row hPL hΩall hAE hcls hP4 hH hGen hV
  exact ⟨hV, hNC, twinYRankOn_psu4_of_p1' hmod hP1, twinYLinkedSU4_of_mod_three p f hmod⟩

end Assemble

end CFSG.ClassicalInvolution.RouteD.TWT4
