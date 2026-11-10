module

public import Certificates.Data.Kernel.Fi22Twist.Bf
public import Certificates.Kernel.Fi22Twist.Data
public import Certificates.Kernel.Sporadic.Fi22.X2069PT
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist

@[expose] noncomputable def ch431009bf_ (k : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 48) k) (fun i => bfK BF CertificateChecks.KernelSpor.Fi22ChT.F i)
    (nat_lit 48)


end CertificateChecks.KernelFi22Twist

#kc_each CertificateChecks.KernelFi22Twist.ch431009bf_ 0 15

end
