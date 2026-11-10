module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerBlocks

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3CH

open CFSG.Open
open scoped MatrixGroups

section Lift

theorem nonempty_equiv_quotient_of_odd_ker {L S : Type} [Group L] [Finite L] [Group S]
    (φ : L →* S) (hφ : Function.Surjective φ) (hodd : Odd (Nat.card φ.ker))
    (e : S ≃* SL(2, ZMod 3)) :
    Nonempty (L ⧸ classicalInvolutionOddCore L ≃* SL(2, ZMod 3)) := by
  have : Finite S := Finite.of_surjective φ hφ
  have hOS : classicalInvolutionOddCore S = ⊥ := by
    have h1 := CFSG.ComponentClassification.OddCore.equiv_invariant e
    have h2 : componentClassificationOddCore SL(2, ZMod 3) = ⊥ := componentOddCore_sl2Three
    rw [h2] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hle : φ.ker ≤ classicalInvolutionOddCore L :=
    CFSG.ComponentClassification.OddCore.maximal L φ.ker φ.normal_ker hodd
  have hge : classicalInvolutionOddCore L ≤ φ.ker := by
    have hN : ((classicalInvolutionOddCore L).map φ).Normal :=
      Subgroup.Normal.map inferInstance φ hφ
    have hNodd : Odd (Nat.card ((classicalInvolutionOddCore L).map φ)) :=
      (CFSG.ComponentClassification.OddCore.odd_card L).of_dvd_nat
        (Subgroup.card_map_dvd (classicalInvolutionOddCore L) φ)
    have h1 : (classicalInvolutionOddCore L).map φ ≤ classicalInvolutionOddCore S :=
      CFSG.ComponentClassification.OddCore.maximal S _ hN hNodd
    rw [hOS, le_bot_iff] at h1
    intro x hx
    have h2 : φ x ∈ (classicalInvolutionOddCore L).map φ := ⟨x, hx, rfl⟩
    rw [h1] at h2
    exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp h2)
  have heq : classicalInvolutionOddCore L = φ.ker := le_antisymm hge hle
  exact ⟨(QuotientGroup.quotientMulEquivOfEq heq).trans
    ((QuotientGroup.quotientKerEquivOfSurjective φ hφ).trans e)⟩

end Lift

section Layer


end Layer

end CFSG.ClassicalInvolution.Q3.Q3CH
