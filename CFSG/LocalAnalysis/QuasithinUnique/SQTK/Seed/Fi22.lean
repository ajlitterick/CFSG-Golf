module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.SimpleTrick
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi22
public import CFSG.Sporadic.Bridge.Fi22Surj
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.QuasithinUnique.SQTK

open TauCeti

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem presentation_eq : SporadicName.Fi22.presentation = Sporadic.fi22Presentation := rfl

theorem nonempty_mulEquiv_carrier_Fi22
    [IsSimpleGroup SporadicName.Fi22.Group] :
    Nonempty (SporadicName.Fi22.Group ≃* Blueprint.NativeSporadic.Carrier .Fi22) := by
  have : Nontrivial CFSG.Sporadic.Fi22.J :=
    nontrivial_of_two_le_natCard (k := 64561751654400) (by norm_num)
      (le_of_eq CFSG.Sporadic.Fi22.card_J.symm)
  obtain ⟨e⟩ := nonempty_mulEquiv_of_relators_two SporadicName.Fi22.presentation
    (by rw [presentation_eq]; exact CFSG.Sporadic.Bridge.Fi22.generatorCount_eq)
    (by rw [presentation_eq]; exact CFSG.Sporadic.Bridge.Fi22.relators_eval)
    CFSG.Sporadic.Fi22.closure_ab
  exact ⟨e.trans CFSG.Sporadic.Fi22.fi22EquivJ.symm⟩


end CFSG.QuasithinUnique.SQTK
