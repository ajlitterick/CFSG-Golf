
module

public import Certificates.Data.Kernel.SporSch.Co2SShape
public import CFSG.Sporadic.Co2Schreier.WitCheckInputs
import CFSG.Certificates.Kernel.Spor.DistinctSound
public import CFSG.Certificates.Kernel.Spor.Co2ChainSound

public section

namespace CFSG.KS.Co2SShape

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2Shape CFSG.Sporadic.Co2Schreier
  CFSG.Sporadic.Co2Cert CFSG.Monster.B.Mathieu CFSG.Monster.B.Co2.Native


theorem extWordsOK_of {k : Nat} {D : List (List Int)} (h : wordsL k D 0 = true) :
    extWordsOK k D = true := by
  unfold extWordsOK
  rw [List.all_eq_true]
  intro t ht
  have := wordsL_spec k D 0 h t (List.mem_range.1 ht)
  rwa [Nat.zero_add, Nat.add_comm] at this

theorem localShapeK_sound {L : LocalCert} (h : localShapeK L = true) : localShapeOK L = true := by
  unfold localShapeK at h
  simp only [bAnd_iff, Nat.beq_eq, lenL_eq, allL_eq, eqNL_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := h
  unfold localShapeOK
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
  simp only [List.all_eq_true, lettersK_eq, Nat.beq_eq, beq_iff_eq] at *
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, extWordsOK_of h10, h11, h12, h13, h14, h15, h16,
    h17, extWordsOK_of h18, h19, h20, h21, h22, h23, h24, chainK_sound h25, chainK_sound h26,
    chainK_sound h27, chainK_sound h28, chainK_sound h29, chainK_sound h30⟩


end CFSG.KS.Co2SShape

end
