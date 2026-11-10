module

public import CFSG.Quasithin.AppendixH.H16.OctadGroup
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.AppendixH.H15.Vocab

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH


theorem mem_octV1_iff (b : W11) : b ∈ octV1 ↔ b = 1 ∨ b = toW 11 3 := by
  rw [octV1, mem_maskSub]
  constructor
  · rintro ⟨m, hm, rfl⟩
    have h : m = 0 ∨ m = 3 := by simpa [oct1Basis, combos] using hm
    rcases h with rfl | rfl
    · left; rw [toW_zero]
    · right; rfl
  · rintro (rfl | rfl)
    · exact ⟨0, zero_mem_combos _, toW_zero 11⟩
    · exact ⟨3, mem_combos_of_mem (by simp [oct1Basis]), rfl⟩

theorem toW_three_ne_one : toW 11 3 ≠ 1 := by
  intro h
  have h' : toW 11 3 = toW 11 0 := by rw [toW_zero]; exact h
  exact absurd (toW_inj (by norm_num) (by norm_num) h') (by norm_num)


end CFSG.ASVolI.H16
