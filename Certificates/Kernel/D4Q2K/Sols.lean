module

public import Certificates.Data.Kernel.D4Q2K.Defs
public import Certificates.Kernel.D4Q2K.Data
public import Certificates.Kernel.D4Q2K.DataS
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4Q2K

open CFSG.KC.D4Q2K

@[expose] noncomputable def solASl (s : Nat) : Bool := solAK D.MF DS.SF DS.sp (Nat.mul 280 s) 280

@[expose] noncomputable def solBSl (s : Nat) : Bool := solBK D.MF DS.SF DS.si (Nat.mul 280 s) 280

#kc_each CertificateChecks.KernelD4Q2K.solASl 0 16
#kc_each CertificateChecks.KernelD4Q2K.solBSl 0 8


end CertificateChecks.KernelD4Q2K

end
