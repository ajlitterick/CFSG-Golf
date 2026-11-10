module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderLinear
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

open CFSG.Open Bender

theorem nestedAt_of_isBenderGroup {X : Type*} [Group X] [Finite X] (hX : fusionIsBenderGroup X)
    (T : Sylow 2 X) : NestedAt (T : Subgroup X) := by
  rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact nestedAt_of_mulEquiv_psl2 hf e T
  · exact nestedAt_of_mulEquiv_psu3 hf e T
  · exact nestedAt_of_mulEquiv_sz ha e T


end CFSG.ComponentClassification.AschbacherToolkit
