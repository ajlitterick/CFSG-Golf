module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic

public section

namespace CFSG.ComponentClassification.CatalogueBGraphField

noncomputable section

open Matrix CatalogueBHigherLinearAction CatalogueBHigherLinearInner CatalogueBUnitaryTwo

universe u


theorem odd_linear_graph_field_involution_fixed_p_components_native
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (p f : ℕ) [Fact p.Prime] (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ f) (hn : 3 ≤ n)
    (A : GL (Fin n) K) (sigma : K ≃+* K) (hne : sigma ≠ 1)
    (_hidentity : graphFieldAction n K A sigma ≠ 1)
    (hsquare : graphFieldAction n K A sigma ^ 2 = 1) :
    Even f ∧ 1 ≤ f / 2 ∧
      ∃ hunitary : Nat.card K = (p ^ (f / 2)) ^ 2,
        unitaryFieldConjugation p (f / 2) hunitary = sigma ∧
        Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma) = p ^ (f / 2) ∧
        3 ≤ Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma) ∧
        ∀ (ell : ℕ), ell.Prime → ∀ L : Subgroup (twistedFixedPSL n K A sigma),
          CFSG.IsPComponent ell L → CFSG.IsQuasisimple L ∧
            Nonempty (L ≃* UnitaryDataProjectiveSpecial n K p (f / 2) hunitary) := by
  obtain ⟨heven, hhalf, hunitary, hbar, _hformula, hfixed, hnq⟩ :=
    odd_graphField_unitary_data n K p f (Fact.out : p.Prime) hpodd hf hcard hn A sigma hne hsquare
  change unitaryFieldConjugation p (f / 2) hunitary = sigma at hbar
  have hthree : 3 ≤ Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma) := by
    rw [hfixed]
    exact odd_prime_power_three_le p (f / 2) Fact.out hpodd hhalf
  refine ⟨heven, hhalf, hunitary, hbar, hfixed, hthree, ?_⟩
  intro ell hell L hL
  have hfull := graphField_involution_fixed_pComponent_projectiveSpecialUnitary
    n K hn A sigma hne hsquare hnq ell hell L hL
  refine ⟨hfull.1, ?_⟩
  change Nonempty (L ≃* ProjectiveSpecialUnitary n K (unitaryFieldConjugation p (f / 2) hunitary))
  rw [hbar]
  exact hfull.2


end

end CFSG.ComponentClassification.CatalogueBGraphField
