module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwModel
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


@[expose] def F4InnerResidualThree :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K →
    ∀ D : Subgroup (MulAut (adjointGroup Tag.F4 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ innerAut (adjointGroup Tag.F4 K) →
      (3 ∣ Nat.card K + 1 ∨ ∀ g : adjointGroup Tag.F4 K,
        ∃ x ∈ D.comap (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)),
          ((g * x * g⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) ∉ torusGroup Tag.F4 K) →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.F4 K)), innerAut (adjointGroup Tag.F4 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.F4 K))) →
          localDeltaIn 3 H D = ⊥

section Twisted


theorem exists_lang_data_F4 (K : Type) [Field K] [Finite K] :
    ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
      ∃ g0 ∈ adjointGroup Tag.F4 (AlgebraicClosure K), Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) f4Neg := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective (ringChar K)
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator Tag.F4 K (ℓ := ringChar K) (f := f) f.pos
    (AlgebraicClosure K) f4Neg
  refine ⟨iterateFrobenius (AlgebraicClosure K) (ringChar K) f, fun c => ?_, g0, hg0C, hg0⟩
  rw [iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]


end Twisted

section Families


end Families

end CFSG.HardMathSupport.Timmesfeld.CrossChar
