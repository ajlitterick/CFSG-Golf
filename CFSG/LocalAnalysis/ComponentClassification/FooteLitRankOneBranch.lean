module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitRankOne
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSol78Inputs

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

theorem card_center_le_two_of_alt_seven (hSA : SolAltLit.SchurAlternatingMultiplierInput)
    {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q) (hZ : IsPGroup 2 (center Q))
    (e : Q ⧸ center Q ≃* alternatingGroup (Fin 7)) : Nat.card (center Q) ≤ 2 := by
  obtain ⟨hperf, -⟩ := hQ
  have hdvd := card_center_dvd_card_hopfMultiplier e
  have h6 : (if 7 = 6 ∨ 7 = 7 then 6 else 2) = 6 := by decide
  rw [(hSA 7 (by norm_num)).2, h6] at hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ
  rw [hk] at hdvd ⊢
  by_contra h
  have h4 : 2 ^ 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by
    by_contra hk2
    exact h (by interval_cases k <;> norm_num))
  have := h4.trans hdvd
  norm_num at this

theorem card_center_le_two_of_footeFamilyType (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (G : Type) [Group G] [Finite G]
    (B : Subgroup G) (hB : ∃ b : G, IsTwoComponentAt b B) (hfam : FooteFamilyType B) :
    Nat.card (center (B ⧸ pPrimeCore 2 B)) ≤ 2 := by
  obtain ⟨b, -, hBC, hBpc⟩ := hB
  have hBq := isQuasisimple_quotient_of_isPComponent hBC hBpc
  have hZp := isPGroup_center_quotient_pPrimeCore ↥B
  obtain ⟨e⟩ := nonempty_fusionZStar_quotient_equiv ↥B
  rcases hfam with ⟨⟨e7⟩⟩ | ⟨p, f, hp, hp2, -, -, hL⟩
  · exact card_center_le_two_of_alt_seven hSA hBq hZp (e.symm.trans e7)
  · exact card_center_le_two_of_lieModel_psl_two hGA hGC hBq hZp e.symm hp hp2 hL


theorem footeRankOneBranch_of_inputs (hLB : FooteLBalanceInput)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) : FooteRankOneBranch :=
  footeRankOneBranch_of_multiplierBound hLB hCI
    (card_center_le_two_of_footeFamilyType hGA hGC hSA)

theorem footeInitialReductions_of_inputs (h1 : FooteOddCoreReduction)
    (h2 : FooteComponentReduction) (h4 : FooteOuterReduction) (hLB : FooteLBalanceInput)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) : FooteInitialReductions :=
  footeInitialReductions_of_steps h1 h2 (footeRankOneBranch_of_inputs hLB hCI hGA hGC hSA) h4

end CFSG.ComponentClassification.FooteLit
