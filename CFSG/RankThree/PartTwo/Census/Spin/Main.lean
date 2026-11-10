module

public import CFSG.RankThree.PartTwo.Census.Assembly
public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeOdd
public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeTwo

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti

theorem spinWitness_typeB (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.B r q).Valid) (hr : 3 ≤ r) (h42 : ¬ (r = 4 ∧ q.p = 2 ∧ q.exponent = 1))
    (h34 : ¬ (r = 3 ∧ q.p = 2 ∧ q.exponent = 2)) (h32 : ¬ (r = 3 ∧ q.p = 2 ∧ q.exponent = 1)) :
    Excluded433 (.lie ⟨.B r q, hv⟩) := by
  have hf1 := q.exponent_pos
  by_cases hp : q.p = 2
  · by_cases hf : 2 ≤ q.exponent
    · exact excluded433_B_even r q hv hr hp hf fun h => h34 ⟨h.1, hp, h.2⟩
    · have hf' : q.exponent = 1 := by omega
      rcases (show r = 3 ∨ r = 4 ∨ 5 ≤ r by omega) with rfl | rfl | h5
      · exact absurd ⟨rfl, hp, hf'⟩ h32
      · exact absurd ⟨rfl, hp, hf'⟩ h42
      · exact excluded433_B_two r q hv hp h5
  · exact excluded433_B_odd r q hv hr hp

theorem spinWitness_typeD (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.D r q).Valid) (h42 : ¬ (r = 4 ∧ q.p = 2 ∧ q.exponent = 1)) :
    Excluded433 (.lie ⟨.D r q, hv⟩) := by
  have hf1 := q.exponent_pos
  by_cases hp : q.p = 2
  · by_cases hf : 2 ≤ q.exponent
    · exact excluded433_D_even r q hv hp hf
    · have hf' : q.exponent = 1 := by omega
      have h4 : 4 ≤ r := TypeDDiagramLieIndex.four_le_rank
        (TypeDLieIndex.toTypeDDiagramLieIndex ⟨⟨.D r q, hv⟩, by simp⟩)
      rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | h5
      · exact absurd ⟨rfl, hp, hf'⟩ h42
      · exact excluded433_D_two r q hv hp h5
  · exact excluded433_D_odd r q hv hp

theorem spinWitness_typeTwistedD (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid) (h42 : ¬ (r = 4 ∧ q.p = 2 ∧ q.exponent = 1)) :
    Excluded433 (.lie ⟨.twistedD r q, hv⟩) := by
  have hf1 := q.exponent_pos
  have h4 : 4 ≤ r := CarrierTD.four_le ⟨⟨.twistedD r q, hv⟩, by simp⟩
  by_cases hp : q.p = 2
  · by_cases hf : 2 ≤ q.exponent
    · by_cases h44 : r = 4 ∧ q.exponent = 2
      · obtain ⟨rfl, he⟩ := h44
        exact excluded433_twistedD_four_four q hv hp he
      · exact excluded433_twistedD_even r q hv hp hf h44
    · have hf' : q.exponent = 1 := by omega
      rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | h5
      · exact absurd ⟨rfl, hp, hf'⟩ h42
      · rcases (show r = 5 ∨ 6 ≤ r by omega) with rfl | h6
        · exact excluded433_twistedD_five_two q hv hp hf'
        · exact excluded433_twistedD_two r q hv hp h6
  · exact excluded433_twistedD_odd r q hv hp


end CFSG.RankThree.PartTwo.Census.Spin
