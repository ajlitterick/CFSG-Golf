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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.ClassicalInvolution.Balance

structure RootFamily (ι V : Type*) [AddCommGroup V] [Module (ZMod 2) V] where
  z : ι → V
  χ : ι → Module.Dual (ZMod 2) V
  symm : ∀ i j, χ i (z j) = χ j (z i)
  closed : ∀ i j, ∃ k, z k = z j + χ i (z j) • z i ∧ χ k = χ j + χ j (z i) • χ i
  conn : ∀ i j, Relation.ReflTransGen (fun i j => χ i (z j) = 1) i j
  span_eq : Submodule.span (ZMod 2) (Set.range z) = ⊤

namespace RootFamily

variable {ι V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (T : RootFamily ι V)

@[expose] def R (a : V) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) (T.z '' {i | T.χ i a = 0})

theorem z_mem_R {a : V} {i : ι} (h : T.χ i a = 0) : T.z i ∈ T.R a :=
  Submodule.subset_span ⟨i, h, rfl⟩

private theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

private theorem add_self_zero (x : V) : x + x = 0 := by
  have : (2 : ZMod 2) • x = 0 := by
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_smul]
  rw [← this, two_smul]

private theorem chi_z_of_closed {p r s k : ι} (hz : T.z k = T.z s + T.χ r (T.z s) • T.z r) :
    T.χ p (T.z k) = T.χ p (T.z s) + T.χ r (T.z s) * T.χ p (T.z r) := by
  rw [hz, map_add, map_smul, smul_eq_mul]

private theorem chi_chi_of_closed {r s k : ι} (hχ : T.χ k = T.χ s + T.χ s (T.z r) • T.χ r)
    (x : V) : T.χ k x = T.χ s x + T.χ s (T.z r) * T.χ r x := by
  rw [hχ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]

private theorem edge {a : V} {p q : ι} (hpa : T.χ p a = 1) (hqa : T.χ q a = 1)
    (hb : T.χ p (T.z q) = 1) : T.z p + T.z q ∈ T.R a := by
  obtain ⟨k, hz, hχ⟩ := T.closed p q
  have hqp : T.χ q (T.z p) = 1 := (T.symm q p).trans hb
  have hka : T.χ k a = 0 := by
    rw [T.chi_chi_of_closed hχ, hqa, hpa, hqp]
    decide
  have hzk : T.z k = T.z p + T.z q := by rw [hz, hb, one_smul, add_comm]
  rw [← hzk]
  exact T.z_mem_R hka

private theorem common {a : V} {p q m : ι} (hpa : T.χ p a = 1) (hqa : T.χ q a = 1)
    (hma : T.χ m a = 0) (hmp : T.χ m (T.z p) = 1) (hmq : T.χ m (T.z q) = 1) :
    T.z p + T.z q ∈ T.R a := by
  rcases zmod2_cases (T.χ p (T.z q)) with hpq | hpq
  · obtain ⟨q₁, hz, hχ⟩ := T.closed m q
    have hq1a : T.χ q₁ a = 1 := by
      rw [T.chi_chi_of_closed hχ, hma, hqa]
      simp
    have hzq1 : T.z q₁ = T.z q + T.z m := by rw [hz, hmq, one_smul]
    have hpm : T.χ p (T.z m) = 1 := (T.symm p m).trans hmp
    have hpq1 : T.χ p (T.z q₁) = 1 := by
      rw [T.chi_z_of_closed hz, hpq, hmq, hpm]
      decide
    have h1 := T.edge hpa hq1a hpq1
    have hmR : T.z m ∈ T.R a := T.z_mem_R hma
    have h2 : T.z p + T.z q = (T.z p + T.z q₁) + T.z m := by
      rw [hzq1]
      calc T.z p + T.z q = T.z p + T.z q + 0 := by rw [add_zero]
        _ = T.z p + T.z q + (T.z m + T.z m) := by rw [add_self_zero]
        _ = (T.z p + (T.z q + T.z m)) + T.z m := by abel
    rw [h2]
    exact Submodule.add_mem _ h1 hmR
  · exact T.edge hpa hqa hpq

private def Walk : ℕ → ι → ι → Prop
  | 0, p, q => p = q
  | n + 1, p, q => ∃ r, T.χ p (T.z r) = 1 ∧ Walk n r q

private theorem key {a : V} :
    ∀ n : ℕ, ∀ p q : ι, T.χ p a = 1 → T.χ q a = 1 → T.Walk n p q → T.z p + T.z q ∈ T.R a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p q hpa hqa hw
    rcases n with _ | d
    · have hpq : p = q := hw
      subst hpq
      rw [add_self_zero]
      exact Submodule.zero_mem _
    · obtain ⟨r, hpr, hw1⟩ := hw
      have hsplit : ∀ x : V, T.z p + T.z q = (T.z p + x) + (x + T.z q) := fun x => by
        calc T.z p + T.z q = T.z p + T.z q + 0 := by rw [add_zero]
          _ = T.z p + T.z q + (x + x) := by rw [add_self_zero]
          _ = (T.z p + x) + (x + T.z q) := by abel
      rcases zmod2_cases (T.χ r a) with hra | hra
      ·
        rcases d with _ | e
        · have hrq : r = q := hw1
          rw [hrq, hqa] at hra
          exact absurd hra (by decide)
        · obtain ⟨s, hrs, hw2⟩ := hw1
          rcases zmod2_cases (T.χ s a) with hsa | hsa
          ·
            rcases e with _ | f
            · have hsq : s = q := hw2
              rw [hsq, hqa] at hsa
              exact absurd hsa (by decide)
            · obtain ⟨t, hst, hw3⟩ := hw2
              rcases zmod2_cases (T.χ p (T.z s)) with hps | hps
              · rcases zmod2_cases (T.χ r (T.z t)) with hrt | hrt
                ·
                  obtain ⟨n', hzn, hχn⟩ := T.closed r s
                  have hpn' : T.χ p (T.z n') = 1 := by
                    rw [T.chi_z_of_closed hzn, hps, hrs, hpr]
                    decide
                  have hn't : T.χ n' (T.z t) = 1 := by
                    rw [T.chi_chi_of_closed hχn, hst, hrt, T.symm s r, hrs]
                    decide
                  exact ih (f + 2) (by omega) p q hpa hqa ⟨n', hpn', ⟨t, hn't, hw3⟩⟩
                · exact ih (f + 2) (by omega) p q hpa hqa ⟨r, hpr, ⟨t, hrt, hw3⟩⟩
              · exact ih (f + 2) (by omega) p q hpa hqa ⟨s, hps, ⟨t, hst, hw3⟩⟩
          ·
            have h1 := T.common hpa hsa hra ((T.symm r p).trans hpr) hrs
            have h2 := ih e (by omega) s q hsa hqa hw2
            rw [hsplit (T.z s)]
            exact Submodule.add_mem _ h1 h2
      ·
        have h1 := T.edge hpa hra hpr
        have h2 := ih d (by omega) r q hra hqa hw1
        rw [hsplit (T.z r)]
        exact Submodule.add_mem _ h1 h2


end RootFamily

end CFSG.ClassicalInvolution.Balance
