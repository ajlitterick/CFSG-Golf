module

public import Certificates.Kernel.L34W.Outer
public import Certificates.Data.Kernel.L34W.Fix
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.L34W.DData

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelL34W.LF CertificateChecks.KernelL34W.lfArr 1
#kmisc_packarrs CertificateChecks.KernelL34W.TY CertificateChecks.KernelL34W.tyArr 2
#kmisc_packarrs CertificateChecks.KernelL34W.DW CertificateChecks.KernelL34W.dArr 10

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34W CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

theorem lf_k : lfOK AlX.F LF = true := by decide +kernel

theorem ty_k : tyOK OT TY = true := by decide +kernel

@[expose] noncomputable def dOK (lo n : Nat) : Bool :=
  allN n fun q => dOne T1X.F AlX.F OT BT LF TY DW (kbMasks.getD (Nat.add lo q) 0) (Nat.add lo q)

theorem d_k0 : dOK 0 5 = true := by decide +kernel

theorem d_k5 : dOK 5 5 = true := by decide +kernel

theorem d_k10 : dOK 10 5 = true := by decide +kernel


end CertificateChecks.KernelL34W

end
