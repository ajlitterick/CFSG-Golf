module

public import CFSG.ClassicalInvolution.Generic.StepLayer
public import CFSG.ClassicalInvolution.Generic.StepQuasisimple
public import CFSG.ClassicalInvolution.LBalance.Main

public section

namespace CFSG.ClassicalInvolution.Generic

open CFSG.Open

variable {p f : ℕ} [Fact p.Prime]

theorem lieSystemMod_of_corefree (hcore : CoreStep p f) (hfund : ClassicalIsFundamental p f)
    (hlift : CentralLift p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Y : Type} [Group Y] [Finite Y]
    (hBelow : CITBelowU p f (Nat.card Y)) (hO : classicalInvolutionOddCore Y = ⊥)
    {Λ : Set (Subgroup Y)} (hΛ : InClass p f Λ) : LieSystemMod p f Λ := by
  by_cases hconn : NonCommConnected Λ
  · exact lieSystemMod_of_quasisimple hcore hfund hlift hp2 hq hBelow hO hΛ
      (isQuasisimple_of_nonCommConnected CFSG.ClassicalInvolution.l2PrimeBalance
        (by omega) hO hΛ hconn)
  · exact lieSystemMod_of_lieSystem_corefree hO (lieSystem_of_not_connected hBelow hO hΛ hconn)

theorem lieSystemMod_of_oddQuotient {Y : Type} [Group Y] [Finite Y]
    (hBelow : CITBelowU p f (Nat.card Y)) (hO : classicalInvolutionOddCore Y ≠ ⊥)
    {Λ : Set (Subgroup Y)} (hΛ : InClass p f Λ) : LieSystemMod p f Λ := by
  have hlt : Nat.card (Y ⧸ classicalInvolutionOddCore Y) < Nat.card Y := by
    have hmul := (classicalInvolutionOddCore Y).card_eq_card_quotient_mul_card_subgroup
    have h1 : 1 < Nat.card (classicalInvolutionOddCore Y) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hO
    have h2 : 0 < Nat.card (Y ⧸ classicalInvolutionOddCore Y) := Nat.card_pos
    nlinarith
  have hmod := hBelow _ hlt (oddQuotientFamily Λ) (inClass_oddQuotient hΛ)
  exact lieSystem_of_lieSystemMod_corefree
    (CFSG.ComponentClassification.OddCore.quotient_corefree Y) hmod

theorem citStepU_of_coreStep (hcore : CoreStep p f) (hfund : ClassicalIsFundamental p f)
    (hlift : CentralLift p) (n : ℕ) : CITStepU p f n := by
  intro hp2 hq hBelow Y _ _ hY Λ hΛ
  have hBelow' : CITBelowU p f (Nat.card Y) := by rw [hY]; exact hBelow
  by_cases hO : classicalInvolutionOddCore Y = ⊥
  · exact lieSystemMod_of_corefree hcore hfund hlift hp2 hq hBelow' hO hΛ
  · exact lieSystemMod_of_oddQuotient hBelow' hO hΛ

theorem citInductiveU_of_coreStep (hcore : CoreStep p f) (hfund : ClassicalIsFundamental p f)
    (hlift : CentralLift p) : CITInductiveU p f :=
  citInductiveU_of_step p f (citStepU_of_coreStep hcore hfund hlift)


end CFSG.ClassicalInvolution.Generic
