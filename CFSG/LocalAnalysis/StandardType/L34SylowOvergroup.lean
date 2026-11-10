
module


public import Certificates.Certificate465003

public section

namespace CFSG.StandardType.L34Sylow

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem overgroupFacts :
    OvergroupFacts :=
  have C := Certificates.certificate465003
  ⟨by rw [closureTabs_gensS]; exact card_S, C.card_P, C.P_le_S, C.aSix, C.trichotomy⟩

end CFSG.StandardType.L34Sylow
