module

public import Certificates.Kernel.Sporadic.Tits.LocK
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSchreierFam.T7450

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSpor
  CertificateChecks.KernelMisc

@[expose] def w7450 : List Int := [4, 3, 4, 1, 4, 3, -4]

@[expose] noncomputable def FI (j : Nat) : Nat := pinvS 1755 11 (mask 11) (TitsText.F j)

@[expose] noncomputable def T : Nat :=
  wordK 1755 11 (mask 11) (pidn 1755 11) TitsText.F FI w7450


end CertificateChecks.KernelSchreierFam.T7450
