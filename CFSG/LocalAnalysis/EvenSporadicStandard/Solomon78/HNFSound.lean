module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFWords
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFTree
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFOrb
public import CFSG.Sporadic.HNSchreier.ArchEq
public import CFSG.Open.MonsterY443Defs

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.HNSchreier CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Sporadic.HNSchreier.Native

@[expose] noncomputable def hnfAB : ℕ → ↥JH := fun h => if h = 0 then aJ else bJ

@[expose] noncomputable def hnfG1 : ↥JH := wordProd hnfAB hnfW1

@[expose] noncomputable def hnfG2 : ↥JH := wordProd hnfAB hnfW2

@[expose] noncomputable def hnfGen : ℕ → ↥JH := fun h =>
  if h = 0 then aJ else if h = 1 then hnfG1 else hnfG2

@[expose] noncomputable def hnfC0 : Subgroup ↥JH := Subgroup.closure {aJ, hnfG1, hnfG2}

section Tables

attribute [local irreducible] pword pcomp pinvCand


theorem hnfW1_ok : plettersOK 2 hnfW1 = true := by decide

theorem hnfW2_ok : plettersOK 2 hnfW2 = true := by decide


variable {tA tAi tB tBi g1 g1i g2 g2i : Array Nat}


end Tables

section State

attribute [local irreducible] pword pcomp pinvCand


end State

section Core

attribute [local irreducible] pword pcomp pinvCand

@[expose] noncomputable def hnfRep (g : List ℤ) : ↥JH := conjBy (wordProd hnfAB g) aJ


theorem plettersOK_iff {j : ℕ} {w : List ℤ} :
    plettersOK j w = true ↔ ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ j := by
  simp [plettersOK, List.all_eq_true]


variable {tA tAi tB tBi g1 g1i g2 g2i : Array Nat}


end Core

section Orbit

attribute [local irreducible] pword pcomp pinvCand


theorem finite_JH : Finite ↥JH := Finite.of_injective permHom permHom_injective

theorem hnfGen_mem {k : ℕ} (hk : k < 3) : hnfGen k ∈ hnfC0 := by
  interval_cases k
  · exact Subgroup.subset_closure (by simp [hnfGen])
  · exact Subgroup.subset_closure (by simp [hnfGen, hnfG1])
  · exact Subgroup.subset_closure (by simp [hnfGen, hnfG2])


end Orbit

end CFSG.EvenSporadicStandard.Solomon78
