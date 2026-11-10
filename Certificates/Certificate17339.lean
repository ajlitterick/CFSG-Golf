module

public import Certificates.Data.TabFi23Y
public meta import Certificates.Data.TabFi23Y
import Certificates.Kernel.Fi23Y322.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi23.Native CFSG.HardMathSupport.Dickson.I271.TabFi23Y in
theorem certificate17339 : fi23YOK (orbitData ()) = true :=
  KernelFi23Y322.yCheck_ok

end Certificates
