
module

public import Certificates.Certificate2022Base
import all Certificates.Certificate2022Base

import Certificates.Kernel.LocalComp.L34Cert

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four in
open CFSG.PSL3Four.Native in
theorem certificate2022 : CFSG.PSL3Four.Native.certificate 20160 241920 1963 = true :=
  KernelLC.L34Cert.certificate_true

end Certificates
