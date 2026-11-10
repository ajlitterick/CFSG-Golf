module

public import CFSG.LocalAnalysis.ComponentClassification.InvolutionLayerOrbitLocation

public section

open CFSG.Open

namespace CFSG.ComponentClassification.ComponentFamilyPumpUpFusion

theorem exists_outside_two {Index : Type*} [Fintype Index]
    (hcard : 3 ≤ Fintype.card Index) (first second : Index) :
    ∃ other : Index, other ≠ first ∧ other ≠ second := by
  classical
  let remainder := (Finset.univ.erase first).erase second
  have hfirstCard : (Finset.univ.erase first).card = Fintype.card Index - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hpositive : 0 < remainder.card := by
    by_cases hsecond : second ∈ Finset.univ.erase first
    · have hcardRemainder := Finset.card_erase_of_mem hsecond
      change remainder.card = (Finset.univ.erase first).card - 1 at hcardRemainder
      omega
    · have heq : remainder = Finset.univ.erase first := Finset.erase_eq_of_notMem hsecond
      rw [heq, hfirstCard]
      omega
  obtain ⟨other, hother⟩ := Finset.card_pos.mp hpositive
  exact ⟨other, (Finset.mem_erase.mp (Finset.mem_erase.mp hother).2).1,
    (Finset.mem_erase.mp hother).1⟩


end CFSG.ComponentClassification.ComponentFamilyPumpUpFusion
