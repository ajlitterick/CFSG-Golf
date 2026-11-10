module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.DecSLSound
public import CFSG.Sporadic.ONOddCore.LiftCountInputs
meta import CFSG.Sporadic.ONOddCore.LiftCountInputs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Misc.KernelRfl

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.LiftsT CFSG.Sporadic.ONOddCore.liftsText

namespace CertificateChecks.KernelSpor.ON2121

open CFSG.Sporadic.ONOddCore CFSG.KS.DecSL

@[expose] def liftE : List (List Nat) :=
  [[0, 3, 1, 2], [], [], [0, 3, 2, 1], [], [], [], [], [], [0, 2, 3, 1], [0, 3, 1, 2], []]

theorem digits : digitsSLOK LiftsT.chars = true := by
  quickRfl

theorem cands_eq : (decodeLifts (natsSL LiftsT.chars)).cands.map liftIdxs = liftE := by
  kernelRfl


end CertificateChecks.KernelSpor.ON2121

end
