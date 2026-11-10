module

public import Certificates.Data.Kernel.E8Seven
public import Certificates.Kernel.E8Seven.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CertificateChecks.E8SevenK

open Certificates.E8Seven.K CFSG.KD.E8Seven

@[expose] noncomputable def c14972e2 (a : Nat) : Bool := chk t2 a

@[expose] noncomputable def c14972e4 (a : Nat) : Bool := chk t4 a

#kc_each c14972e2 0 7
#kc_each c14972e4 0 7


end CertificateChecks.E8SevenK
