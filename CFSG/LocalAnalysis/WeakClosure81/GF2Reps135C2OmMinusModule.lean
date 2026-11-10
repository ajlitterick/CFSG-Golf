module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusData
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusRep
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusSingle
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusOuterFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mModule
import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open scoped Matrix TensorProduct

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

private theorem omMinusTwo_two_mul_finrank_range_le {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] {T : Module.End (ZMod 2) V} (hT : T * T = 1) :
    2 * Module.finrank (ZMod 2) (LinearMap.range (T - 1)) ≤ Module.finrank (ZMod 2) V := by
  have : Module.Finite (ZMod 2) V := Module.finite_iff_finite.mpr inferInstance
  have hle : LinearMap.range (T - 1) ≤ LinearMap.ker (T - 1) := by
    rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    have hTT : T (T x) = x := by
      have h := LinearMap.congr_fun hT x
      simpa using h
    show (T - 1) ((T - 1) x) = 0
    rw [LinearMap.sub_apply, Module.End.one_apply, LinearMap.sub_apply, Module.End.one_apply,
      map_sub, hTT]
    rw [show x - T x - (T x - x) = (x + x) - (T x + T x) by abel]
    rw [show x + x = 0 from by
        rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 by decide, zero_smul],
      show T x + T x = 0 from by
        rw [← two_smul (ZMod 2) (T x), show (2 : ZMod 2) = 0 by decide, zero_smul],
      sub_self]
  have hrank := Submodule.finrank_mono hle
  have hrn := LinearMap.finrank_range_add_finrank_ker (T - 1)
  omega

private theorem omMinusTwo_n_ne_one (i : Fin 3) : (o8mDatum hirrQ).n i ≠ 1 := by
  intro h
  have hXY : (o8mDatum hirrQ).X i ≤ (o8mDatum hirrQ).Y i := by
    intro x hx
    have hx' := (o8mDatum hirrQ).n_conjX i x hx
    rwa [h, one_mul, inv_one, mul_one] at hx'
  have hUL : (o8mDatum hirrQ).X i ≤ (o8mDatum hirrQ).U ⊓ (o8mDatum hirrQ).L :=
    le_inf ((o8mDatum hirrQ).X_le i) (hXY.trans ((o8mDatum hirrQ).Y_le i))
  rw [(o8mDatum hirrQ).U_inf_L] at hUL
  exact (o8mDatum hirrQ).X_ne_bot i (le_bot_iff.mp hUL)

private theorem omMinusTwo_n0_sq : (o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 0 = 1 := by
  rw [o8mDatum_n hirrQ 0, minusWeyl_of_lt 4 hirrQ (k := 0) (by norm_num)]
  rw [(minusFrame 4 b c).toHypFrame.longWeyl_mul_self
    (succ_ne_of_lt 4 (k := 0) (by norm_num)) true false]
  have hneg : (-1 : Kˣ) = 1 := by
    apply Units.ext
    simp [CharTwo.neg_eq]
  rw [hneg, map_one]


include hirrQ in
private theorem omMinusTwo_card_endRing_eq_two_of_small (hK : Nat.card K = 2) {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V} (hρ : IsSimpleRep ρ)
    (s : V ≃ₗ[ZMod 2] V) (hs : ∀ v, s (s v) = v) (α : MulAut (spinGroup (quadMinus 4 K b c)))
    (hα : ∀ g v, s (ρ g (s.symm v)) = ρ (α g) v) (hα2 : α * α = 1)
    (houter : ∀ g₀ : spinGroup (quadMinus 4 K b c), α ≠ MulAut.conj g₀)
    (hsmall : 2 * Module.finrank (ZMod 2) (LinearMap.range (s.toLinearMap - 1)) <
      Module.finrank (ZMod 2) V) :
    Nat.card (Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus 4 K b c)))
      ρ.asModule) = 2 := by
  have hρirr : ρ.IsIrreducible :=
    (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).2 hρ
  have hsymm : s.symm = s := by
    ext v
    have h := congrArg s.symm (hs v)
    simpa using h.symm
  have hN : ∀ g, ∃ g', ∀ w, s (ρ g (s w)) = ρ g' w := by
    intro g
    exact ⟨α g, fun w => by simpa [hsymm] using hα g w⟩
  have hcomm := commute_endRing_of_two_mul_finrank_range_lt ρ hρirr s hs hN hsmall
  exact omMinus_two_card_endRing_eq_two_of_outer hirrQ hK hρirr s α hα hα2 houter hcomm


include hirrQ in
theorem omMinus_two_outer_natural_or_four_le (hK : Nat.card K = 2) {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V} (hρ : IsSimpleRep ρ)
    (hρ1 : ∃ g, ρ g ≠ 1) (s : V ≃ₗ[ZMod 2] V) (hs : ∀ v, s (s v) = v)
    (α : MulAut (spinGroup (quadMinus 4 K b c))) (hα : ∀ g v, s (ρ g (s.symm v)) = ρ (α g) v)
    (hα2 : α * α = 1) (houter : ∀ g₀ : spinGroup (quadMinus 4 K b c), α ≠ MulAut.conj g₀) :
    (∃ f : V →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K), f ≠ 0 ∧ ∀ g v, f (ρ g v) = mat 4 g *ᵥ f v) ∨
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (s.toLinearMap - 1)) := by
  by_cases hnat : ∃ f : V →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K),
    f ≠ 0 ∧ ∀ g v, f (ρ g v) = mat 4 g *ᵥ f v
  · exact Or.inl hnat
  · refine Or.inr ?_
    by_cases hsmall : 2 * Module.finrank (ZMod 2) (LinearMap.range (s.toLinearMap - 1)) <
        Module.finrank (ZMod 2) V
    · have hE :=
        omMinusTwo_card_endRing_eq_two_of_small hirrQ hK hρ s hs α hα hα2 houter hsmall
      exact omMinus_two_outer_four_le hirrQ hK hρ hρ1 hE hnat s α hα hα2 houter
    · have hge : Module.finrank (ZMod 2) V ≤
          2 * Module.finrank (ZMod 2) (LinearMap.range (s.toLinearMap - 1)) := not_lt.mp hsmall
      have : Module.Finite (ZMod 2) V := Module.finite_iff_finite.mpr inferInstance
      have hdim8 : 8 ≤ Module.finrank (ZMod 2) V := by
        have hrep := omMinus_two_natural_or_four_le hirrQ hK hρ hρ1
          (omMinusTwo_n0_sq hirrQ) (omMinusTwo_n_ne_one hirrQ 0)
        rcases hrep with hnat' | hfour
        · exact absurd hnat' hnat
        · have hT : ρ ((o8mDatum hirrQ).n 0) * ρ ((o8mDatum hirrQ).n 0) = 1 := by
            rw [← map_mul, omMinusTwo_n0_sq hirrQ, map_one]
          have hbound := omMinusTwo_two_mul_finrank_range_le
            (T := ρ ((o8mDatum hirrQ).n 0)) hT
          omega
      omega

end CFSG.LocalAnalysis.WeakClosure81
