module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFSetup

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.HNSchreier CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Sporadic.HNSchreier.Native

@[expose] noncomputable def hnfStabElem (k : ℕ) : ↥JH := wordProd hnfGen hnfStabWords[k]!


theorem hnfStabWords_ok : ∀ k < 2, plettersOK 3 hnfStabWords[k]! = true := by decide


theorem wordProd_mem_hnfC0 {w : List ℤ} (hw : plettersOK 3 w = true) :
    wordProd hnfGen w ∈ hnfC0 := by
  induction w with
  | nil => simp [wordProd]
  | cons l w ih =>
    have hw' := plettersOK_iff.1 hw
    have hl := hw' l (List.mem_cons_self)
    have hrest : plettersOK 3 w = true :=
      plettersOK_iff.2 fun x hx => hw' x (List.mem_cons_of_mem _ hx)
    rw [wordProd_cons]
    refine mul_mem ?_ (ih hrest)
    unfold letterVal
    by_cases hpos : 0 < l
    · rw [ite_eq_left hpos]
      exact hnfGen_mem (by omega)
    · rw [ite_eq_right hpos]
      exact inv_mem (hnfGen_mem (by omega))

theorem hnfStabElem_mem {k : ℕ} (hk : k < 2) : hnfStabElem k ∈ hnfC0 :=
  wordProd_mem_hnfC0 (hnfStabWords_ok k hk)

section Stab

attribute [local irreducible] pword pcomp pinvCand


end Stab

end CFSG.EvenSporadicStandard.Solomon78
