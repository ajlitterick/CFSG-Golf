module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatStatement
public import CFSG.Sporadic.Schreier.TitsInner

public section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

@[expose] def CatSLmEvenOuterFamilyAt (τ : StatedLieTag) (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ n e : ℕ, StatedLieAdmissible τ n 2 e → LieModel S τ n 2 e →
    ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D →
      LieModel (D ⧸ center D) .PSL m 2 f → FixedCentralizerTwoFree σ D →
        LieModel S .PSL m 2 (2 * f)


theorem catSLmEvenOuterAt_of_families {m : ℕ} (h : ∀ τ, CatSLmEvenOuterFamilyAt τ m) :
    CatSLmEvenOuterAt m := by
  intro S _ _ hS hna heven σ hσ hout f D hD hDm hodd
  obtain ⟨τ, n, e, hadm, hmS⟩ := heven
  exact h τ S hS hna n e hadm hmS σ hσ hout f D hD hDm hodd


theorem catSLmEvenOuterFamily_of_not_admissible {τ : StatedLieTag}
    (hτ : ∀ n e : ℕ, ¬ StatedLieAdmissible τ n 2 e) (m : ℕ) : CatSLmEvenOuterFamilyAt τ m :=
  fun _ _ _ _ _ n e hadm => absurd hadm (hτ n e)

theorem catSLmEvenOuterFamily_POmegaOdd (m : ℕ) : CatSLmEvenOuterFamilyAt .POmegaOdd m :=
  catSLmEvenOuterFamily_of_not_admissible (τ := .POmegaOdd) (fun _ _ hadm => hadm.2.2.2 rfl) m

theorem catSLmEvenOuterFamily_twistedG2 (m : ℕ) : CatSLmEvenOuterFamilyAt .twistedG2 m :=
  catSLmEvenOuterFamily_of_not_admissible (τ := .twistedG2)
    (fun _ _ hadm => absurd hadm.2.2.2.1 (by norm_num)) m

theorem catSLmEvenOuterFamily_of_involutions_inner {τ : StatedLieTag}
    (hτ : ∀ (K : Type) [Group K] (n e : ℕ), StatedLieAdmissible τ n 2 e → LieModel K τ n 2 e →
      ∀ α : MulAut K, α ^ 2 = 1 → α ∈ (MulAut.conj : K →* MulAut K).range) (m : ℕ) :
    CatSLmEvenOuterFamilyAt τ m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout
  exact absurd (hτ S n e hadm hmS σ (hσ ▸ pow_orderOf_eq_one σ)) hout

section SuzukiReeTits


theorem catSLmEvenOuterFamily_twistedB2 (m : ℕ) : CatSLmEvenOuterFamilyAt .twistedB2 m := by
  refine catSLmEvenOuterFamily_of_involutions_inner (τ := .twistedB2) (fun K _ n e _ hmK => ?_) m
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K e (Or.inl ?_)
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h

theorem catSLmEvenOuterFamily_twistedF4 (m : ℕ) : CatSLmEvenOuterFamilyAt .twistedF4 m := by
  refine catSLmEvenOuterFamily_of_involutions_inner (τ := .twistedF4) (fun K _ n e _ hmK => ?_) m
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K e
    (Or.inr (Or.inl ?_))
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem catSLmEvenOuterFamily_Tits (m : ℕ) : CatSLmEvenOuterFamilyAt .Tits m := by
  refine catSLmEvenOuterFamily_of_involutions_inner (τ := .Tits) (fun K _ n e hadm hmK => ?_) m
  obtain rfl : e = 1 := hadm.2.2.2.2
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K 1
    (Or.inr (Or.inr ?_))
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem catSLmEvenOuterAt_of_open_families {m : ℕ} (hPSL : CatSLmEvenOuterFamilyAt .PSL m)
    (hPSU : CatSLmEvenOuterFamilyAt .PSU m) (hPSp : CatSLmEvenOuterFamilyAt .PSp m)
    (hOp : CatSLmEvenOuterFamilyAt .POmegaPlus m) (hOm : CatSLmEvenOuterFamilyAt .POmegaMinus m)
    (hG2 : CatSLmEvenOuterFamilyAt .G2 m) (hF4 : CatSLmEvenOuterFamilyAt .F4 m)
    (hE6 : CatSLmEvenOuterFamilyAt .E6 m) (hE7 : CatSLmEvenOuterFamilyAt .E7 m)
    (hE8 : CatSLmEvenOuterFamilyAt .E8 m) (h2E6 : CatSLmEvenOuterFamilyAt .twistedE6 m)
    (h3D4 : CatSLmEvenOuterFamilyAt .trialityD4 m) : CatSLmEvenOuterAt m := by
  apply catSLmEvenOuterAt_of_families
  intro τ
  cases τ
  · exact hPSL
  · exact hPSU
  · exact hPSp
  · exact catSLmEvenOuterFamily_POmegaOdd m
  · exact hOp
  · exact hOm
  · exact hG2
  · exact hF4
  · exact hE6
  · exact hE7
  · exact hE8
  · exact h2E6
  · exact h3D4
  · exact catSLmEvenOuterFamily_twistedB2 m
  · exact catSLmEvenOuterFamily_twistedG2 m
  · exact catSLmEvenOuterFamily_twistedF4 m
  · exact catSLmEvenOuterFamily_Tits m


end SuzukiReeTits

end CFSG.SeitzReduction.LinearPilot
