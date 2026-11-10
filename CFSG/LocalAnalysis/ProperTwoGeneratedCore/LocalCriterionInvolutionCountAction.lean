module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransportAction
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount

open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport

universe u v w

abbrev orderedDistinctPairs (Ω : Type v) : Type v :=
  {p : Ω × Ω // p.1 ≠ p.2}

theorem card_eq_card_mul_constant_fiber
    {A : Type u} {B : Type v} [Finite A] [Finite B]
    (f : A → B) (m : ℕ) (hf : ∀ b : B, Nat.card {a : A // f a = b} = m) :
    Nat.card A = Nat.card B * m := by
  classical
  let := Fintype.ofFinite B
  calc
    Nat.card A = Nat.card (Σ b : B, {a : A // f a = b}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ b : B, Nat.card {a : A // f a = b} := Nat.card_sigma
    _ = Nat.card B * m := by simp only [hf, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Nat.card_eq_fintype_card]

theorem orderedDistinctPairs_card (Ω : Type v) [Finite Ω] :
    Nat.card (orderedDistinctPairs Ω) = Nat.card Ω * (Nat.card Ω - 1) := by
  classical
  let := Fintype.ofFinite Ω
  let e : orderedDistinctPairs Ω ≃ Σ a : Ω, {b : Ω // a ≠ b} :=
    { toFun := fun p => ⟨p.val.1, p.val.2, p.property⟩
      invFun := fun p => ⟨(p.1, p.2.val), p.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc (a : Ω) : Nat.card {b : Ω // a ≠ b} = Nat.card Ω - 1 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype_eq'] using
      Fintype.card_subtype_compl (fun b : Ω => a = b)
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card]

variable {G : Type u} [Group G] {Ω : Type v} [MulAction Gᵐᵒᵖ Ω]

instance orderedDistinctPairsAction : MulAction Gᵐᵒᵖ (orderedDistinctPairs Ω) where
  smul g p := ⟨(g • p.val.1, g • p.val.2), fun heq =>
    p.property (by
      have hh := congrArg (fun a : Ω => g⁻¹ • a) heq
      simpa only [inv_smul_smul] using hh)⟩
  one_smul p := Subtype.ext (Prod.ext (one_smul _ _) (one_smul _ _))
  mul_smul g h p := Subtype.ext (Prod.ext (mul_smul _ _ _) (mul_smul _ _ _))


end CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount
