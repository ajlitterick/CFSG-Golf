module

public import Certificates.Data.Kernel.D4Q2K.Defs
public import Certificates.Kernel.D4Q2K.DataC
public import Certificates.Kernel.D4Q2K.DataS
public import Certificates.Kernel.D4Q2K.DataT
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4Q2K

open CFSG.KC.D4Q2K

@[expose] noncomputable def triCSl (s : Nat) : Bool := triCK DS.SF DT.TF DC.cl (Nat.mul 20 s) 20

#kc_each CertificateChecks.KernelD4Q2K.triCSl 0 112


end CertificateChecks.KernelD4Q2K

end
