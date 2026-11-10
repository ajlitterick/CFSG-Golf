
module

public import Certificates.Data.TabFi23C
public meta import Certificates.Data.TabFi23C
import Certificates.Kernel.Fi23Tw.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi23.Native CFSG.HardMathSupport.Dickson.I271.TabFi23C in
theorem certificate17340 : fi23COK (orbitData ()) = true :=
  KernelFi23Tw.fi23C_ok

end Certificates
