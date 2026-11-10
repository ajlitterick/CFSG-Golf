module

import Certificates.Kernel.J4Q.FormInv
public import Certificates.Certificate3084Base

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.J4.Native in
theorem certificate10059 :
    eqRows (mulRows formRows (invRows formRows)) idRows = true := KernelJ4Q.form_inverse_check

end Certificates
