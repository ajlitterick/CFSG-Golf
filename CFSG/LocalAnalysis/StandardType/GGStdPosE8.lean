module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
import CFSG.LocalAnalysis.StandardType.GGStdPosE8Core
import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE8

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem ggKGPosStdPosE8 :
    GGKGPosStdPosCase .E8 (fun _ _ => True) := by
  rintro G _ _ p Bs X n f ψ h -
  obtain ⟨⟨hp, hp2, hadm, -⟩, ⟨hker, hX, -, hpq⟩, ⟨hBs, -, -⟩, hinn, hc, -⟩ := h
  obtain ⟨-, hf, -⟩ := hadm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hF]; exact hpq
  have hT : GGExcToralRankInput .E8 (GaloisField 2 f) p := by
    by_cases hp3 : p = 3
    · subst hp3
      exact TableBExc.Three.ggExcToralRankInput_E8_three hpF
    · exact ggExcToralRankInput_E8_of_ne_three hp hp2 hp3 hpF
  have hT8 : ¬ GGKGPosTorsion p .E8 n := by
    rintro (⟨h', -⟩ | ⟨h', -⟩) <;> cases h'
  subst hX
  exact StdPosExc.exists_stdPos_e8 hker hBs hinn (hc hT8) hT

end CFSG.StandardType

end
