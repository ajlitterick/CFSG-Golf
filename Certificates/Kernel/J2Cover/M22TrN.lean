module

public import Certificates.Kernel.J2Cover.M22TrK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def fR7P (m : Nat) : Bool := fR7 (R7P 0) m

@[expose] noncomputable def fT7P (m : Nat) : Bool := fT7 (R7P 0) m

#lc_blocks R7B fR7P 16384 1024

#lc_blocks TPB fT7P 384 16


end CertificateChecks.KernelJ2Cover

end
