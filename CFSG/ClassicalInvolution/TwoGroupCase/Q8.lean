module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ClassicalInvolution

open QuaternionGroup

def q8Eval {H : Type*} [Group H] (u v : H) : QuaternionGroup 2 → H
  | .a k => u ^ k.val
  | .xa k => v * u ^ k.val

theorem q8Eval_eq {H : Type*} [Group H] (f : QuaternionGroup 2 →* H) (x : QuaternionGroup 2) :
    f x = q8Eval (f (a 1)) (f (xa 0)) x := by
  have ha : ∀ k : ZMod 4, (a k : QuaternionGroup 2) = (a 1) ^ k.val := fun k => by
    rw [a_one_pow, ZMod.natCast_zmod_val]
  cases x with
  | a k =>
    calc f (a k) = f ((a 1) ^ k.val) := by rw [ha k]
      _ = (f (a 1)) ^ k.val := map_pow _ _ _
  | xa k =>
    have h : (xa k : QuaternionGroup 2) = xa 0 * a k := by simp
    calc f (xa k) = f (xa 0) * f ((a 1) ^ k.val) := by rw [h, map_mul, ha k]
      _ = f (xa 0) * (f (a 1)) ^ k.val := by rw [map_pow]

private def Q8AutPair (u v : QuaternionGroup 2) : Prop :=
  (∀ x y, q8Eval u v (x * y) = q8Eval u v x * q8Eval u v y) ∧
    ∀ x y, q8Eval u v x = q8Eval u v y → x = y

private instance (u v : QuaternionGroup 2) : Decidable (Q8AutPair u v) := by
  unfold Q8AutPair; infer_instance

private theorem q8AutPair_of_mulEquiv (β : QuaternionGroup 2 ≃* QuaternionGroup 2) :
    Q8AutPair (β (a 1)) (β (xa 0)) := by
  have e : ∀ x, β x = q8Eval (β (a 1)) (β (xa 0)) x := fun x => q8Eval_eq β.toMonoidHom x
  refine ⟨fun x y => ?_, fun x y h => β.injective ?_⟩
  · rw [← e, ← e, ← e, map_mul]
  · rw [e x, e y]; exact h


private theorem q8_aut_aux : ∀ u₁ u₂ : QuaternionGroup 2, Q8AutPair u₁ u₂ →
    ∀ v₁ v₂ : QuaternionGroup 2, Q8AutPair v₁ v₂ →
    (∀ x, q8Eval u₁ u₂ (q8Eval u₁ u₂ x) = q8Eval v₁ v₂ (q8Eval v₁ v₂ x)) →
    (∃ x, q8Eval u₁ u₂ (q8Eval u₁ u₂ x) ≠ x) →
    ¬ ∀ x, q8Eval u₁ u₂ (q8Eval v₁ v₂ (q8Eval u₁ u₂ x)) = q8Eval v₁ v₂ x := by
  decide +kernel

theorem q8_not_faithful_on_aut
    (f : QuaternionGroup 2 →* (QuaternionGroup 2 ≃* QuaternionGroup 2)) :
    ¬ Function.Injective f := by
  intro hf
  have h2 : (a 2 : QuaternionGroup 2) ≠ 1 := by decide
  have e1 : (a 1 : QuaternionGroup 2) * a 1 = a 2 := by decide
  have e2 : (xa 0 : QuaternionGroup 2) * xa 0 = a 2 := by decide
  have e3 : (a 1 : QuaternionGroup 2) * xa 0 * a 1 = xa 0 := by decide
  set u := f (a 1) with hu
  set v := f (xa 0) with hv
  have euu : u * u = v * v := by rw [hu, hv, ← map_mul, ← map_mul, e1, e2]
  have euu1 : u * u ≠ 1 := by
    rw [hu, ← map_mul, e1]
    intro h
    exact h2 (hf (by rw [map_one]; exact h))
  have euvu : u * v * u = v := by rw [hu, hv, ← map_mul, ← map_mul, e3]
  have eu : ∀ x, u x = q8Eval (u (a 1)) (u (xa 0)) x := fun x => q8Eval_eq u.toMonoidHom x
  have ev : ∀ x, v x = q8Eval (v (a 1)) (v (xa 0)) x := fun x => q8Eval_eq v.toMonoidHom x
  refine q8_aut_aux _ _ (q8AutPair_of_mulEquiv u) _ _ (q8AutPair_of_mulEquiv v) ?_ ?_ ?_
  · intro x
    rw [← eu, ← eu, ← ev, ← ev]
    simpa using congrArg (fun γ : QuaternionGroup 2 ≃* QuaternionGroup 2 => γ x) euu
  · by_contra hcon
    push Not at hcon
    refine euu1 (MulEquiv.ext fun x => ?_)
    have := hcon x
    rw [← eu, ← eu] at this
    simpa using this
  · intro x
    rw [← eu, ← eu, ← ev, ← ev]
    simpa using congrArg (fun γ : QuaternionGroup 2 ≃* QuaternionGroup 2 => γ x) euvu

private theorem q8_card_autPairs :
    Fintype.card {p : QuaternionGroup 2 × QuaternionGroup 2 // Q8AutPair p.1 p.2} = 24 := by
  decide +kernel

theorem q8_natCard_mulEquiv_le : Nat.card (QuaternionGroup 2 ≃* QuaternionGroup 2) ≤ 24 := by
  let f : (QuaternionGroup 2 ≃* QuaternionGroup 2) →
      {p : QuaternionGroup 2 × QuaternionGroup 2 // Q8AutPair p.1 p.2} :=
    fun β => ⟨(β (a 1), β (xa 0)), q8AutPair_of_mulEquiv β⟩
  have hf : Function.Injective f := by
    intro β γ h
    have h1 : β (a 1) = γ (a 1) := congrArg (fun p => p.1.1) h
    have h2 : β (xa 0) = γ (xa 0) := congrArg (fun p => p.1.2) h
    refine MulEquiv.ext fun x => ?_
    calc β x = q8Eval (β (a 1)) (β (xa 0)) x := q8Eval_eq β.toMonoidHom x
      _ = q8Eval (γ (a 1)) (γ (xa 0)) x := by rw [h1, h2]
      _ = γ x := (q8Eval_eq γ.toMonoidHom x).symm
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card (α := {p : QuaternionGroup 2 × QuaternionGroup 2 //
    Q8AutPair p.1 p.2}), q8_card_autPairs] at this

theorem q8_center_mem_ker {M : Type*} [Group M] (f : QuaternionGroup 2 →* M)
    (hf : ¬ Function.Injective f) : f (a 2) = 1 := by
  have hq : ∀ g : QuaternionGroup 2, g ≠ 1 → g = a 2 ∨ g ^ 2 = a 2 := by decide
  unfold Function.Injective at hf
  push Not at hf
  obtain ⟨x, y, hxy, hne⟩ := hf
  have hg : f (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have hne' : x⁻¹ * y ≠ 1 := fun h => hne (inv_mul_eq_one.mp h)
  rcases hq _ hne' with h | h
  · rw [← h]; exact hg
  · rw [← h, map_pow, hg, one_pow]


theorem q8_not_faithful_perm {n : ℕ} (hn : n < 8) (f : QuaternionGroup 2 →* Equiv.Perm (Fin n)) :
    ¬ Function.Injective f := by
  intro hf
  have h2 : (a 2 : QuaternionGroup 2) ≠ 1 := by decide
  have hmove : ∃ p, f (a 2) p ≠ p := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    apply h2
    apply hf
    ext p
    simp [h p]
  obtain ⟨p, hp⟩ := hmove
  have hq : ∀ g : QuaternionGroup 2, g ≠ 1 → g = a 2 ∨ g ^ 2 = a 2 := by decide
  have hstab : ∀ g : QuaternionGroup 2, f g p = p → g = 1 := by
    intro g hg
    by_contra hne
    rcases hq g hne with h | h
    · subst h; exact hp hg
    · apply hp
      rw [← h, map_pow, pow_two, Equiv.Perm.mul_apply, hg, hg]
  have hinj : Function.Injective (fun g : QuaternionGroup 2 => f g p) := by
    intro g h hgh
    have h1 : f (h⁻¹ * g) p = p := by
      simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
      simp only at hgh
      rw [hgh]
      simp
    exact (inv_mul_eq_one.mp (hstab _ h1)).symm
  have hc := Fintype.card_le_of_injective _ hinj
  rw [QuaternionGroup.card] at hc
  simp at hc
  omega

end CFSG.ClassicalInvolution
