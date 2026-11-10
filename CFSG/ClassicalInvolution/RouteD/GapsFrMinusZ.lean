module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusLeaf
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleMinus

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.RootSystem
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.CurtisTits CFSG.Timmesfeld QuadraticMap

section Lift

variable {p f : ℕ} [Fact p.Prime]

theorem minusLift_of_chain_long (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {u : ℕ} {X : Type} [Group X]
    (θ : spinGroup (quadMinus (u + 3 + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus (u + 3 + 5) (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {R : ℕ → Subgroup (spinGroup (quadMinus (u + 3 + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))}
    {Rtw RM : Subgroup (spinGroup (quadMinus (u + 3 + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))}
    (hRf : ∀ a ≤ u + 3, R a ∈ fundamentalSubgroups .POmegaMinus
      (minusDatum (u + 3 + 5) (minusCoeffs_irr p f)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaMinus
      (minusDatum (u + 3 + 5) (minusCoeffs_irr p f)))
    (hRMf : RM ∈ fundamentalSubgroups .POmegaMinus (minusDatum (u + 3 + 5) (minusCoeffs_irr p f)))
    (hadj : ∀ a < u + 3, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < u + 3, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ u + 3 → Commutes (R a) (R b))
    (hM : ∀ a ≤ u + 3, Commutes RM (R a))
    (hadjtw : ModelAdj (Subgroup.center _) (R (u + 2)) Rtw)
    (hcommtw : ∀ a, a ≤ u + 1 → Commutes (R a) Rtw) (hcommtw' : Commutes (R (u + 3)) Rtw)
    (hne : Rtw ≠ R (u + 3))
    (hfix : ∀ a, 1 ≤ a → a ≤ u + 3 → ∀ y ∈ R a, σ (θ y) = θ y)
    (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y) (hfixM : ∀ y ∈ RM, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ∃ (x : spinGroup (quadMinus (u + 3 + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) (t : Bool),
      (∀ a (ha : a ≤ u + 3), R a = ((rootSL2 (minusFrame (u + 3 + 5) (minusCoeffs p f).1
        (minusCoeffs p f).2).toHypFrame a (a + 1) (by omega) (by omega) (by omega) true false).map
          (MulAut.conj x).toMonoidHom)) ∧
      Rtw = ((rootSL2 (minusFrame (u + 3 + 5) (minusCoeffs p f).1
        (minusCoeffs p f).2).toHypFrame (u + 3) (u + 3 + 1) (by omega) (by omega) (by omega) true
          true).map (MulAut.conj x).toMonoidHom) ∧
      RM = ((rootSL2 (minusFrame (u + 3 + 5) (minusCoeffs p f).1
        (minusCoeffs p f).2).toHypFrame (u + 3 + 2) (u + 3 + 3) (by omega) (by omega) (by omega)
          true t).map (MulAut.conj x).toMonoidHom) ∧ MinusLift θ σ := by
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaMinus (u + 3 + 5) p f :=
    ⟨Fact.out, hf1, by show 4 ≤ u + 3 + 5; omega⟩
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have cq := Exotic.centralQuot_minus hp2 hq hadm
  have hdim : 9 ≤ Module.finrank (GaloisField p f)
      (Fin (u + 3 + 5 - 1) ⊕ Fin (u + 3 + 5 - 1) ⊕ Fin 2 → GaloisField p f) := by
    rw [finrank_minus p f _ (by omega)]
    omega
  have hQ : (quadMinus (u + 3 + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadMinus_of_finite _ (GaloisField p f) (minusCoeffs_irr p f))
  obtain ⟨hdist, htwin⟩ := chain_distinct_twin_gen hp2 hq hdim cq hRf hRtwf hadj hcomm hadjtw
    hcommtw hcommtw'
  obtain ⟨x, hxR, hxtw, t, hxM⟩ := spin_chain_recognition_gen hp2 hq hQ (s := u + 3) (by omega)
    (minusFrame (u + 3 + 5) (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame hdim cq hRf hRtwf
    hRMf hadj hlin hcomm hM hdist hne htwin
  exact ⟨x, t, hxR, hxtw, hxM, (toralNormal_minus_of_frame_chain hp2 hq (s := u + 3) (by omega) θ
    hker σ hσ2 hσr x t hxR hxtw hxM hfix hfixtw hfixM hnorm0).2⟩

end Lift

local macro "fr_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

section Main


end Main

end CFSG.ClassicalInvolution.RouteD.Gaps
