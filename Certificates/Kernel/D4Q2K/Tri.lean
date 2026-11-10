module

public import Certificates.Data.Kernel.D4Q2K.Defs
public import Certificates.Kernel.D4Q2K.Data
public import Certificates.Kernel.D4Q2K.DataT
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4Q2K

open CFSG.KC.D4Q2K

@[expose] noncomputable def triSSl (s : Nat) : Bool := triSK D.RF D.MF DT.TW (Nat.mul 280 s) 280

@[expose] noncomputable def tfSl (s : Nat) : Bool := tfK DT.TW DT.TF (Nat.mul 280 s) 280

#kc_each CertificateChecks.KernelD4Q2K.triSSl 0 16
#kc_each CertificateChecks.KernelD4Q2K.tfSl 0 16


end CertificateChecks.KernelD4Q2K

end
