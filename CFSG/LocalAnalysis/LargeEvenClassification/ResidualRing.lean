module

public import CFSG.LocalAnalysis.LargeEvenClassification.FrattiniExact

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def ResidualRing (_twist : ZMod 4) := (ZMod 4 × ZMod 4) × (ZMod 4 × ZMod 4)

@[expose] def residualAdd {twist : ZMod 4} (first second : ResidualRing twist) : ResidualRing twist :=
  ((first.1.1 + second.1.1, first.1.2 + second.1.2),
    (first.2.1 + second.2.1, first.2.2 + second.2.2))

instance residualRingAdd (twist : ZMod 4) : Add (ResidualRing twist) := ⟨residualAdd⟩

instance residualRingZero (twist : ZMod 4) : Zero (ResidualRing twist) := ⟨((0, 0), (0, 0))⟩

instance residualRingNeg (twist : ZMod 4) : Neg (ResidualRing twist) :=
  inferInstanceAs (Neg ((ZMod 4 × ZMod 4) × (ZMod 4 × ZMod 4)))

instance residualRingOne (twist : ZMod 4) : One (ResidualRing twist) := ⟨((1, 0), (0, 1))⟩

@[expose] def residualMultiply (twist : ZMod 4) (first second : ResidualRing twist) : ResidualRing twist :=
  ((first.1.1 * second.1.1 + twist * first.1.2 * second.2.1,
    first.1.1 * second.1.2 + first.1.2 * second.2.2),
    (first.2.1 * second.1.1 + first.2.2 * second.2.1,
      twist * first.2.1 * second.1.2 + first.2.2 * second.2.2))

instance residualRingMul (twist : ZMod 4) : Mul (ResidualRing twist) := ⟨residualMultiply twist⟩

instance residualRingRing (twist : ZMod 4) : Ring (ResidualRing twist) :=
  Ring.ofMinimalAxioms
    (by
      intro first second third
      change residualAdd (residualAdd first second) third = residualAdd first (residualAdd second third)
      apply Prod.ext <;> apply Prod.ext <;> simp only [residualAdd, add_assoc])
    (by
      intro element
      change residualAdd ((0, 0), (0, 0)) element = element
      apply Prod.ext <;> apply Prod.ext <;> simp only [residualAdd, zero_add])
    (by
      intro element
      change residualAdd ((-element.1.1, -element.1.2), (-element.2.1, -element.2.2)) element =
        ((0, 0), (0, 0))
      apply Prod.ext <;> apply Prod.ext <;> simp only [residualAdd, neg_add_cancel])
    (by
      rintro ⟨⟨firstA, firstB⟩, ⟨firstC, firstD⟩⟩ ⟨⟨secondA, secondB⟩, ⟨secondC, secondD⟩⟩
        ⟨⟨thirdA, thirdB⟩, ⟨thirdC, thirdD⟩⟩
      change residualMultiply twist (residualMultiply twist _ _) _ =
        residualMultiply twist _ (residualMultiply twist _ _)
      apply Prod.ext <;> apply Prod.ext <;> simp only [residualMultiply] <;> ring)
    (by
      rintro ⟨⟨firstA, firstB⟩, ⟨firstC, firstD⟩⟩
      change residualMultiply twist ((1, 0), (0, 1)) ((firstA, firstB), (firstC, firstD)) = _
      simp only [residualMultiply, one_mul, zero_mul, mul_zero, add_zero, zero_add]
      rfl)
    (by
      rintro ⟨⟨firstA, firstB⟩, ⟨firstC, firstD⟩⟩
      change residualMultiply twist ((firstA, firstB), (firstC, firstD)) ((1, 0), (0, 1)) = _
      simp only [residualMultiply, mul_one, mul_zero, add_zero, zero_add]
      rfl)
    (by
      rintro ⟨⟨firstA, firstB⟩, ⟨firstC, firstD⟩⟩ ⟨⟨secondA, secondB⟩, ⟨secondC, secondD⟩⟩
        ⟨⟨thirdA, thirdB⟩, ⟨thirdC, thirdD⟩⟩
      change residualMultiply twist _ (residualAdd _ _) =
        residualAdd (residualMultiply twist _ _) (residualMultiply twist _ _)
      apply Prod.ext <;> apply Prod.ext <;> dsimp only [residualMultiply, residualAdd] <;> ring)
    (by
      rintro ⟨⟨firstA, firstB⟩, ⟨firstC, firstD⟩⟩ ⟨⟨secondA, secondB⟩, ⟨secondC, secondD⟩⟩
        ⟨⟨thirdA, thirdB⟩, ⟨thirdC, thirdD⟩⟩
      change residualMultiply twist (residualAdd _ _) _ =
        residualAdd (residualMultiply twist _ _) (residualMultiply twist _ _)
      apply Prod.ext <;> apply Prod.ext <;> dsimp only [residualMultiply, residualAdd] <;> ring)

instance residualRingFintype (twist : ZMod 4) : Fintype (ResidualRing twist) :=
  inferInstanceAs (Fintype ((ZMod 4 × ZMod 4) × (ZMod 4 × ZMod 4)))

instance residualRingDecidableEq (twist : ZMod 4) : DecidableEq (ResidualRing twist) :=
  inferInstanceAs (DecidableEq ((ZMod 4 × ZMod 4) × (ZMod 4 × ZMod 4)))

@[expose] def residualDeterminant {twist : ZMod 4} (element : ResidualRing twist) : ZMod 4 :=
  element.1.1 * element.2.2 - twist * element.1.2 * element.2.1

theorem residualDeterminant_mul {twist : ZMod 4} (first second : ResidualRing twist) :
    residualDeterminant (first * second) = residualDeterminant first * residualDeterminant second := by
  rcases first with ⟨⟨firstA, firstB⟩, ⟨firstC, firstD⟩⟩
  rcases second with ⟨⟨secondA, secondB⟩, ⟨secondC, secondD⟩⟩
  change residualDeterminant (residualMultiply twist _ _) = _
  dsimp only [residualDeterminant, residualMultiply]
  ring

theorem residual_unit_determinant {twist : ZMod 4} (unit : (ResidualRing twist)ˣ) :
    residualDeterminant unit.val = 1 ∨ residualDeterminant unit.val = 3 := by
  have hproduct : residualDeterminant unit.val * residualDeterminant (unit⁻¹).val = 1 := by
    rw [← residualDeterminant_mul, Units.mul_inv]
    change (1 : ZMod 4) * 1 - twist * 0 * 0 = 1
    simp
  have hcases : ∀ first second : ZMod 4, first * second = 1 → first = 1 ∨ first = 3 := by decide
  exact hcases _ _ hproduct

abbrev ResidualUnitCandidates (twist : ZMod 4) := {element : ResidualRing twist //
  residualDeterminant element = 1 ∨ residualDeterminant element = 3}

@[expose] def residualUnitCandidate {twist : ZMod 4} (unit : (ResidualRing twist)ˣ) :
    ResidualUnitCandidates twist := ⟨unit.val, residual_unit_determinant unit⟩

theorem residualUnitCandidate_injective {twist : ZMod 4} :
    Function.Injective (residualUnitCandidate (twist := twist)) := by
  intro first second heq
  exact Units.ext (congrArg Subtype.val heq)


@[expose] def residualInverse {twist : ZMod 4} (element : ResidualRing twist) : ResidualRing twist :=
  ((residualDeterminant element * element.2.2, -residualDeterminant element * element.1.2),
    (-residualDeterminant element * element.2.1, residualDeterminant element * element.1.1))

set_option maxRecDepth 10000 in
theorem residualUnitCandidate_surjective {twist : ZMod 4} :
    Function.Surjective (residualUnitCandidate (twist := twist)) := by
  intro candidate
  have hinverse : candidate.val * residualInverse candidate.val = 1 ∧
      residualInverse candidate.val * candidate.val = 1 := by
    have hcertificate : ∀ (coefficient : ZMod 4) (element : ResidualRing coefficient),
        (residualDeterminant element = 1 ∨ residualDeterminant element = 3) →
          element * residualInverse element = 1 ∧ residualInverse element * element = 1 := by
      decide
    exact hcertificate twist candidate.val candidate.property
  refine ⟨⟨candidate.val, residualInverse candidate.val, hinverse.1, hinverse.2⟩, ?_⟩
  apply Subtype.ext
  rfl


theorem residual_unit_card_eq_even {twist : ZMod 4} (htwist : twist = 0 ∨ twist = 2) :
    Nat.card (ResidualRing twist)ˣ = 64 := by
  rw [Nat.card_congr (Equiv.ofBijective residualUnitCandidate
    ⟨residualUnitCandidate_injective, residualUnitCandidate_surjective⟩)]
  rcases htwist with rfl | rfl <;> rw [Nat.card_eq_fintype_card] <;> decide

theorem residual_unit_card_eq_one : Nat.card (ResidualRing 1)ˣ = 96 := by
  rw [Nat.card_congr (Equiv.ofBijective residualUnitCandidate
    ⟨residualUnitCandidate_injective, residualUnitCandidate_surjective⟩), Nat.card_eq_fintype_card]
  decide


universe groupUniverse


end CFSG.LargeEvenClassification.Helpers
