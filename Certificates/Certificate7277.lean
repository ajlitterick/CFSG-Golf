module

import Certificates.Kernel.ASVolI.K43Checks7277
import Certificates.Kernel.HMathieu.T24Glue
import CFSG.Certificates.Kernel.ASVolI.K43Sound7277
import CFSG.Certificates.Kernel.Common.ForallTree
public import Certificates.Data.Kernel.ASVolI.K43K7277
import CFSG.Certificates.Kernel.LocalCompTits.Span
import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1

public section

namespace CertificateChecks.KernelASVolI

#kc_forall_tree k43f4_all (fun i => CFSG.KS.ASVolI.f4Slice i = true) 32
  CertificateChecks.KernelASVolI.k43f4_

end CertificateChecks.KernelASVolI

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelHMathieu

theorem certificate7277 :
    CFSG.ASVolI.K43Data.listsOK () = true ∧
    CFSG.ASVolI.K43Data.f3OK () = true ∧
    CFSG.ASVolI.K43Data.f4OK () = true :=
  ⟨CFSG.KS.ASVolI.listsOK_of_K T24.packed T24.idOK KernelASVolI.k43_listsS
      KernelASVolI.k43_listsK,
    CFSG.KS.ASVolI.f3OK_of_K T24.packed KernelASVolI.k43_f3S KernelASVolI.k43_f3K,
    CFSG.KS.ASVolI.f4OK_of_K KernelASVolI.k43_f4S KernelASVolI.k43f4_all⟩

end Certificates
