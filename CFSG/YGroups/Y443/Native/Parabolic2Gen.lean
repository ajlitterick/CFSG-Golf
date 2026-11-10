module

public import CFSG.Monster.AxisCount.HSCount
public import CFSG.YGroups.Y443.Native.AlignConj

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short CFSG.Open CFSG.YGroups.Y443Native

theorem mem_shortClass_of_conj {W c : SpaceB ≃ₗ[ℚ] SpaceB} (hW : W ∈ Gmat)
    (h : W * c * W⁻¹ = tStar) : c ∈ shortClass :=
  ⟨W⁻¹, inv_mem hW, by rw [← h]; group⟩

theorem eq_conj_of_conj {W c t : SpaceB ≃ₗ[ℚ] SpaceB} (h : W * c * W⁻¹ = t) :
    c = W⁻¹ * t * W := by
  rw [← h]
  group


theorem evalGL_slet_eq :
    evalGL slet = ((fM y443C : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) := by
  rw [fM_y443C_eq, wcWord, wordLin_wcWordOf slet slet_le]

theorem omega_conj_slet :
    wordLin omegaWord * evalGL slet * (wordLin omegaWord)⁻¹ = tStar := by
  rw [evalGL_slet_eq]
  exact omega_conj

theorem evalGL_slet_eq_conj :
    evalGL slet = (wordLin omegaWord)⁻¹ * tStar * wordLin omegaWord :=
  eq_conj_of_conj omega_conj_slet

end CFSG.YGroups.Y443
