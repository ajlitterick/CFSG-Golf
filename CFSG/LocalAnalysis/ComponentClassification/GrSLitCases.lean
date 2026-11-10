module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSFMReduction

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.GSLit

@[expose] def LocalBalanceCase : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X → LocallyTwoBalanced X

@[expose] def HeldCase : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ OutcomeLocal.UOutcome X → LocallyTwoBalanced X →
    ¬ ∃ (t : X) (L : Subgroup X), orderOf t = 2 ∧ L ≤ centralizer ({t} : Set X) ∧
      IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set X))) ∧
      Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He)

@[expose] def L34Case : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X → LocallyTwoBalanced X →
    (¬ ∃ (t : X) (L : Subgroup X), orderOf t = 2 ∧ L ≤ centralizer ({t} : Set X) ∧
      IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set X))) ∧
      Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He)) →
    ¬ ∃ (x y : X) (L : Subgroup X), GSUnbalancingTriple x y L ∧
      Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 3 2 2

theorem grslit_of_cases (hLB : LocalBalanceCase) (hHe : HeldCase) (hL34 : L34Case) :
    GriessSolomonInput := by
  rintro X _ _ _ hnonab hK hz hU ⟨x, y, L, hT, htype⟩
  have hloc := hLB X hnonab hK hz hU
  have hnoHe := hHe X hnonab hK hU hloc
  rcases htype with hHeL | h34
  · exact hnoHe ⟨x, L, hT.1, hT.2.2.2.1, hT.2.2.2.2.1, hHeL⟩
  · exact hL34 X hnonab hK hz hU hloc hnoHe ⟨x, y, L, hT, h34⟩


end CFSG.ComponentClassification.GrSLit
