module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDNodes
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6NoCover

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (NoCover)

variable {p f : ℕ} [Fact p.Prime]

theorem spinMinus6Generated_galois (hp2 : p ≠ 2) :
    SpinMinus6Generated (minusCoeffs_irr p f) :=
  CFSG.ClassicalInvolution.WeakCT.spinMinusModel_blocks_sup_eq_top (minusCoeffs_irr p f)
    (Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p f) p]; exact hp2))

theorem spinMinus6_noCover_galois (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    NoCover.{0} Odd (spinGroup (quadMinus 3 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  exact CFSG.ClassicalInvolution.WeakCT.spinMinus6_noCover_odd hp2 hF (by rw [hF]; exact hq)
    (minusCoeffs_irr p f)


end CFSG.ClassicalInvolution.RouteD
