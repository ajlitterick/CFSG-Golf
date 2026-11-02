module

public import CFSG.ClassicalInvolution.SmallCases.NDBD4Defs
public import CFSG.ClassicalInvolution.SmallCases.NDBD4Card
public import CFSG.ClassicalInvolution.SmallCases.NDBF
public import CFSG.ClassicalInvolution.Asc77.AscBSE7

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance

variable {p f : ℕ} [Fact p.Prime]

theorem noD4Twins_of (h : D4FiveCore p f) : NoD4Twins p f := by
  intro G _ _ _ K z hS hTT D i hi
  have hno := fuzzyFrameExcluded G K z hS
  let C := Cover.toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D
  obtain ⟨T₁, h₁, T₂, h₂, h1K, h2K, h12, h1z, h2z⟩ := hTT
  have hD4 : C.D.tag i = .POmegaPlus := hi.1
  have hrank : C.D.rank i = 4 := hi.2
  have hQ : ¬ (C.D.tag i = .PSL ∧ C.D.rank i = 2) := fun h' => by
    rw [hD4] at h'
    exact absurd h'.1 (by decide)
  have h4 : 4 ≤ C.D.card := D4.four_le_card C h₁ h₂ h1K h2K h12 h1z h2z hQ
  rcases (by omega : C.D.card = 4 ∨ C.D.card = 5 ∨ 6 ≤ C.D.card) with h4' | h5 | h6
  · exact Asc77.BSC.BSE.false_of_d4_four (C := C) hno (b := i) hD4 hrank h4'
  · exact h G K z hS.nonabelian hS.odd hS.five hS.member hS.below hS.dconn hno D i hi h5
  · exact Asc77.BSC.BSE.false_of_d4_many (C := C) hno (b := i) hD4 hrank h6

end CFSG.ClassicalInvolution.NDB
