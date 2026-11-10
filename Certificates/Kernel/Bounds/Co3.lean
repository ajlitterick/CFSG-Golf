module

public import Certificates.Kernel.Bounds.Data.Co3
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.Co3Alt.All

public section

namespace CertificateChecks.KernelBounds.Co3

theorem t1 : CFSG.KBRoute.Co3Alt.T1.ok = true := by kb_assemble Co3_T1v
theorem t2 : CFSG.KBRoute.Co3Alt.T2.ok = true := by kb_assemble Co3Alt_T2v
theorem t3 : CFSG.KBRoute.Co3Alt.T3.ok = true := by kb_assemble Co3Alt_T3v

open CFSG.KBRoute.Co3Alt in
theorem facts_holds : CFSG.KBRoute.Co3Alt.facts :=
  ⟨t1, t2, t3, top, link_T1, link_T2⟩

end CertificateChecks.KernelBounds.Co3
