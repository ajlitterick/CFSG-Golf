module

public import Certificates.Kernel.J4Q.X0
public import CFSG.Sporadic.J4.QT2LocCntNative
import Certificates.Kernel.J4Q.Strs
public import CFSG.Certificates.Kernel.J4Q.RepQT

public section

set_option maxRecDepth 400000

#j4q_strs CFSG.KD.J4Q.OR CFSG.Sporadic.J4.QT.orbits

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem tMasks_eq : tMasks = fstsK (ptsK OR.s0) := by
  rw [fstsK_eq, ← ptsOfString_ofList]
  unfold tMasks
  rw [OR.eq]
  rfl

theorem zMasks_eq : zMasks = fstsK (ptsK OR.s1) := by
  rw [fstsK_eq, ← ptsOfString_ofList]
  unfold zMasks
  rw [OR.eq]
  rfl

end CertificateChecks.KernelJ4Q

end
