
module

public import Certificates.Certificate3042Base

import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Unitary CFSG.KC.Bfs CFSG.KC.Enum CFSG.KS
  CFSG.KS.Raw CFSG.Certificates.Native

namespace CertificateChecks.Batch3042

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Unitary CFSG.KC.Bfs CFSG.KC.Enum CFSG.KS
  CFSG.KS.Raw CFSG.Certificates.Native

set_option maxRecDepth 100000

open CertificateChecks.Chain3042

end CertificateChecks.Batch3042

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Unitary in
theorem certificate3042 : (certOK amul permGens idArr p2Cert = true)
    ∧ (p2Cert.pts.size = 40320) := CertificateChecks.Batch3042.p2

end Certificates
