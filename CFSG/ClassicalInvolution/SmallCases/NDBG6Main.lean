module

public import CFSG.ClassicalInvolution.SmallCases.NDBG6Swap
public import CFSG.ClassicalInvolution.SmallCases.NDBG2

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.AS76b (Asc75Theorem4)

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime]

theorem NDBG.false_of_g2_of_card_ne_three (hp3 : p ≠ 3) {G : Type} [Group G] [Finite G]
    {K : Subgroup G} {z : G} (C : XCtx p f (𝒞 K) z)
    (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) {b : Fin C.D.card}
    (hG2 : C.D.tag b = .G2) (hcard : 3 ≤ C.D.card) : False := by
  rcases (show C.D.card = 3 ∨ 3 < C.D.card by omega) with h | h
  · exact NDBG.false_of_g2_twin_of_ne_three hp3 C hno hG2 h
  · exact BSC.BSE.false_of_g2_of_card (C := C) hno (b := b) hG2 h

end CFSG.ClassicalInvolution.NDB
