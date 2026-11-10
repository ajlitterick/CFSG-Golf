module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.SimpleTrick
public import CFSG.LocalAnalysis.SectionRank.Sporadic.McL
public import CFSG.Sporadic.Bridge.McLSurj
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.QuasithinUnique.SQTK

open TauCeti

private theorem presentation_eq : SporadicName.McL.presentation = Sporadic.mclPresentation := rfl

theorem nonempty_mulEquiv_carrier_McL
    [IsSimpleGroup SporadicName.McL.Group] :
    Nonempty (SporadicName.McL.Group ≃* Blueprint.NativeSporadic.Carrier .McL) := by
  have : Nontrivial CFSG.Sporadic.McL.J :=
    nontrivial_of_two_le_natCard (k := 898128000) (by norm_num)
      (le_of_eq CFSG.Sporadic.McL.card_J.symm)
  obtain ⟨e⟩ := nonempty_mulEquiv_of_relators_two SporadicName.McL.presentation
    (by rw [presentation_eq]; exact CFSG.Sporadic.Bridge.McL.generatorCount_eq)
    (by rw [presentation_eq]; exact CFSG.Sporadic.Bridge.McL.relators_eval)
    CFSG.Sporadic.McL.closure_ab
  exact ⟨e.trans CFSG.Sporadic.McL.mclEquivJ.symm⟩


end CFSG.QuasithinUnique.SQTK
