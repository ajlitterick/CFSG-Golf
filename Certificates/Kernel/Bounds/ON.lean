module

public import Certificates.Kernel.Bounds.Data.ON
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.ON.All

public section

namespace CertificateChecks.KernelBounds.ON

theorem t1 : CFSG.KBRoute.ON.T1.ok = true := by kb_assemble ON_T1v
theorem t2 : CFSG.KBRoute.ON.T2.ok = true := by kb_assemble ON_T2v
theorem t3 : CFSG.KBRoute.ON.T3.ok = true := by kb_assemble ON_T3v

open CFSG.KBRoute.ON in
theorem facts_holds : CFSG.KBRoute.ON.facts :=
  ⟨t1, t2, t3, top, link_T1, link_T2⟩

end CertificateChecks.KernelBounds.ON
