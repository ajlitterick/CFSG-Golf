module

public import CFSG.GH74.GLS.C3.Layer1.Thm1Fusion
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1
open scoped commutatorElement

theorem pLayerOf_eq_bot_of_solvable {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : Group.IsSolvable ↥H) : pLayerOf 2 H = ⊥ := by
  have hempty : {L : Subgroup G | IsPCompIn 2 H L} = ∅ := by
    ext L
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hL
    obtain ⟨Kh, hKh, -, -, -⟩ := hL.2
    have hquot : Group.IsSolvable (↥H ⧸ pPrimeCore 2 ↥H) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥H))
    have hKsolv : Group.IsSolvable ↥Kh :=
      Group.isSolvable_of_isSolvable_injective Kh.subtype_injective
    exact LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hKh.1 hKsolv
  unfold pLayerOf
  rw [hempty, sSup_empty]


end CFSG.GH74.GLS
