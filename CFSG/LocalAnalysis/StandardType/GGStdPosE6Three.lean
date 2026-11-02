module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
import CFSG.LocalAnalysis.StandardType.GGStdPosE6ThreeCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem ggKGPosStdPosE6Three :
    GGKGPosStdPosCase .E6 (fun p _ => p = 3) := by
  rintro G _ _ p Bs X n f ψ h rfl
  obtain ⟨⟨-, -, hadm, -⟩, ⟨hker, hX, -, hpq⟩, ⟨hBs, hBN, -⟩, hinn, -, hc⟩ := h
  obtain ⟨-, hf, -⟩ := hadm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h3 : 3 ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hF]; exact hpq
  subst hX
  exact StdPosExc.exists_stdPos_e6_three h3 hker hBs hBN hinn hc

end CFSG.StandardType

end
