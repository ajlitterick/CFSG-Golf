module

public import CFSG.YGroups.Y433.Bound
public import CFSG.YGroups.DCE.B433MaximalInputs
public import Certificates.Certificate9354

public section

namespace CFSG.YGroups.DCE.B433

open CFSG.YGroups.DCE.B433Native


theorem psi_range_maximal
    (hG : 4154781481226426191177580544000000 ≤ Nat.card B433)
    (L : Subgroup B433) (hL : psi.range ≤ L) : L = psi.range ∨ L = ⊤ :=
  Certificates.certificate9354 hG L hL

end CFSG.YGroups.DCE.B433
