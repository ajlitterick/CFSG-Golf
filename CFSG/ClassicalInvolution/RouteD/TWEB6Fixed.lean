module

public import CFSG.ClassicalInvolution.RouteD.TWEB6Layer
public import CFSG.ClassicalInvolution.RouteD.TWEB6Sign
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Twin
public import CFSG.ClassicalInvolution.RouteD.GapsFrModel

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B6

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (polarNondegOn_sup)

set_option linter.unusedSectionVars false

section Model

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_orth_ext (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (p : ℕ → HypPair Q) (n : ℕ) (ho : ∀ a b, a < n → b < n → a ≠ b → (p a).Orth (p b)) :
    ∀ m : ℕ, 2 * (n + m) + 1 ≤ Module.finrank K V →
      ∃ p' : ℕ → HypPair Q, (∀ a < n, p' a = p a) ∧
        ∀ a b, a < n + m → b < n + m → a ≠ b → (p' a).Orth (p' b) := by
  intro m
  induction m with
  | zero => exact fun _ => ⟨p, fun _ _ => rfl, ho⟩
  | succ m ih =>
    intro hd
    obtain ⟨p', hp', ho'⟩ := ih (by omega)
    obtain ⟨q, hq⟩ := exists_pair_perp_fam hodd hQ p' (n + m) ho' (by omega)
    refine ⟨fun k => if k = n + m then q else p' k, fun a ha => ?_, fun a b ha hb hab => ?_⟩
    · have : a ≠ n + m := by omega
      simp [this, hp' a ha]
    · by_cases h1 : a = n + m
      · have h2 : b ≠ n + m := fun h => hab (h1.trans h.symm)
        simp only [h1, h2, ite_true, ite_false]
        exact (hq b (by omega)).symm
      · by_cases h2 : b = n + m
        · simp only [h1, h2, ite_true, ite_false]
          exact hq a (by omega)
        · simp only [h1, h2, ite_false]
          exact ho' a b (by omega) (by omega) hab

theorem commutes_frames_of_orth {P₁ P₂ R₁ R₂ : HypPair Q} (h₁₂ : P₁.Orth P₂) (hR : R₁.Orth R₂)
    (o₁₁ : P₁.Orth R₁) (o₁₂ : P₁.Orth R₂) (o₂₁ : P₂.Orth R₁) (o₂₂ : P₂.Orth R₂) :
    Commutes (mkFrame P₁ P₂ h₁₂).La.range (oFrame true R₁ R₂ hR).La.range := by
  refine commutes_of_span_orth _ _ ?_
  rw [frame_span_eq, frame_span_eq]
  simp only [oFrame, mkFrame, twistPair, ite_true, hypPlane_swapPair]
  exact polar_eq_zero_of_sup (fun x hx y hy => polar_hypPlane_of_orth o₁₁ x hx y hy)
    (fun x hx y hy => polar_hypPlane_of_orth o₁₂ x hx y hy)
    (fun x hx y hy => polar_hypPlane_of_orth o₂₁ x hx y hy)
    (fun x hx y hy => polar_hypPlane_of_orth o₂₂ x hx y hy)


end Model

section Spin


end Spin

section Group

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal


end Group

end CFSG.ClassicalInvolution.RouteD.TWE.B6
