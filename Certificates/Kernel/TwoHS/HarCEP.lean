module

public import Certificates.Kernel.TwoHS.HarCK
public import Certificates.Data.Kernel.Spor.PEnumC
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PEnumC

@[expose] noncomputable def ch7291pe (k : Nat) : Bool :=
  penumSlC 3 6 TE.cnt TE.T TE.PL TE.POS TECl TE.SRT TE.SRI (Nat.mul 128 k) 128

theorem ch7291t0 : cnK (TE.T 0) = true := by
  quickRfl


end CFSG.KD.TwoHS

#kc_each CFSG.KD.TwoHS.ch7291pe 0 8

end
