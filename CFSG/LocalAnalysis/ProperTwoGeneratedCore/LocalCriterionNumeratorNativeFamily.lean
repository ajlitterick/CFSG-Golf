module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorNativeAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull

universe u

theorem native_family_matches_exact_borel_degree
    {F : Type u} [Group F] [Finite F] (a i : ℕ) (ha : 2 ≤ a)
    (hmodel : IsSimpleBenderGroupAtExponent a F)
    (B : Subgroup F) (hB : IsBorelSubgroup B)
    (hindex : B.index = (2 ^ a) ^ i + 1) :
    (i = 1 ∧ Nonempty (F ≃* PSL2BinaryMatrixGroup a)) ∨
      (i = 2 ∧ ∃ m : ℕ, a = 2 * m + 1 ∧
        Nonempty (F ≃* SuzukiMatrixGroup m)) ∨
      (i = 3 ∧ ∃ (E : Type) (_ : Field E) (_ : Finite E)
        (J : HermitianForm 3 E),
        J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
        Nat.card E = (2 ^ a) ^ 2 ∧
        Nat.card {x : E // J.conj x = x} = 2 ^ a ∧
        Nonempty (F ≃* ProjectiveSpecialUnitaryMatrixGroup J)) := by
  have htwo : 2 ≤ 2 ^ a := by
    have hpow := Nat.pow_le_pow_right (n := 2) (by omega) ha
    omega
  rcases hmodel with ⟨⟨e⟩⟩ | ⟨⟨m, ham, ⟨e⟩⟩⟩ |
    ⟨⟨E, hfield, hfinite, J, hJ, hEcard, hfixed, ⟨e⟩⟩⟩
  · let K := BinaryGaloisField a
    let T := Matrix.ProjGenLinGroup (Fin 2) K
    let : Finite T := Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
    obtain ⟨ePGL⟩ := psl_charTwo_equiv_pgl a (by omega)
    have hactual := (borel_index_and_whole_involution_card_map_mulEquiv
      (e.trans ePGL) (2 ^ a) 1
      (fun C hC => linear_borel_index_and_whole_involution_parameter a ha C hC) B hB).1
    have hi : i = 1 := Nat.pow_right_injective htwo
      (Nat.add_right_cancel (hindex.symm.trans hactual))
    exact Or.inl ⟨hi, ⟨e⟩⟩
  · have hm : 1 ≤ m := by omega
    have hactual : B.index = (2 ^ a) ^ 2 + 1 := by
      rw [ham]
      exact (borel_index_and_whole_involution_card_map_mulEquiv e
        (2 ^ (2 * m + 1)) 2
        (fun C hC => suzuki_borel_index_and_whole_involution_parameter m hm C hC) B hB).1
    have hi : i = 2 := Nat.pow_right_injective htwo
      (Nat.add_right_cancel (hindex.symm.trans hactual))
    exact Or.inr (Or.inl ⟨hi, m, ham, ⟨e⟩⟩)
  · let := hfield
    let := hfinite
    let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_injective
      (fun x : ProjectiveSpecialUnitaryMatrixGroup J =>
        (x : Matrix.ProjGenLinGroup (Fin 3) E)) Subtype.coe_injective
    have hactual := (borel_index_and_whole_involution_card_map_mulEquiv e
      (2 ^ a) 3
      (fun C hC => unitary_borel_index_and_whole_involution_parameter
        J a ha hEcard hfixed hJ C hC) B hB).1
    have hi : i = 3 := Nat.pow_right_injective htwo
      (Nat.add_right_cancel (hindex.symm.trans hactual))
    exact Or.inr (Or.inr ⟨hi, E, hfield, hfinite, J, hJ, hEcard, hfixed, ⟨e⟩⟩)


end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
