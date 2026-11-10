module

public import Certificates.Kernel.Bounds.Data.M23
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.M23.All

public section

namespace CertificateChecks.KernelBounds.M23

theorem t1 : CFSG.KBRoute.M23.T1.ok = true := by kb_assemble M23_T1v

open CFSG.KBRoute.M23 in
theorem facts_holds : CFSG.KBRoute.M23.facts := ⟨t1, top, power⟩

end CertificateChecks.KernelBounds.M23
