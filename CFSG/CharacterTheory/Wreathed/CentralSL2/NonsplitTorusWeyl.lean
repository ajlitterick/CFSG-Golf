module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.NonsplitCharacters

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

theorem two_ne_zero_of_not_isSquare {F : Type} [Field F] [Finite F] {b : Fˣ}
    (hb : ¬ IsSquare b) : (2 : F) ≠ 0 := by
  apply Ring.two_ne_zero
  intro hc
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two hc (b : F)
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  exact hb ⟨Units.mk0 s hs0, Units.ext (by simpa using hs)⟩

theorem cyclicGenerator_pow_m_mem_nonsplitTorus {F : Type} [Field F] [Fintype F] {b : Fˣ}
    {m : ℕ} {hm : 0 < m} {heven : Even m} {E : Type} [Field E] [Algebra F E]
    {basis : Module.Basis (Fin 2) F E} (h2 : (2 : F) ≠ 0) :
    cyclicGenerator F b m hm heven ^ m ∈ nonsplitTorus F b m hm heven E basis := by
  rw [← nonsplitDiag_negOneE (hm := hm) (heven := heven) (basis := basis) h2]
  exact nonsplitDiag_mem _


end CFSG.Wreathed.CentralSL2
