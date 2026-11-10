module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KFixMain
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs


theorem eq_one_of_mem_commutator_of_field {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) {α : MulAut Y} (hc : α ∈ commutator (MulAut Y))
    (hf : IsFieldAutThree α) : α = 1 := by
  rcases hf with h | hL | hU
  · exact h
  · obtain ⟨F, _, _, e, σ, γ, he⟩ := fieldAutPSL3_data hL
    refine eq_one_of_inndiag_model hY (goodPinned_psl F) e ?_ (Or.inr (Or.inl hL))
    exact (goodPinned_psl F).down
      (map_mem_commutator_mulAut ((MulAut.congr e).toMonoidHom.comp (centerDescend Y)) hc)
  · obtain ⟨p, f, F, _, hF, e, σ, γ, -, he⟩ := fieldAutPSU3_data hU
    have hq := two_lt_pow_of_quasisimple hY hF e
    refine eq_one_of_inndiag_model hY (goodPinned_psu hF hq) e ?_ (Or.inr (Or.inr hU))
    exact (goodPinned_psu hF hq).down
      (map_mem_commutator_mulAut ((MulAut.congr e).toMonoidHom.comp (centerDescend Y)) hc)

theorem inndiagFieldTrivial_l514V : InndiagFieldTrivial innAutDerivedVocab :=
  fun _ _ _ hY _ hf hmem =>
    eq_one_of_mem_commutator_of_field hY (innAutDerivedVocab_le_commutator hY hmem) hf

theorem inputL3fix_l514V : InputL3fix innAutDerivedVocab :=
  inputL3fix_of_inndiagFieldTrivial inndiagFieldTrivial_l514V

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
