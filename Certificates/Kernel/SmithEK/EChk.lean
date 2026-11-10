module

public import Certificates.Kernel.SmithEK.EData

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

theorem c21265pts : c8PtsK (cs.L.getD 0 []) (cs.L.getD 1 []) c8c.Q = true := by
  decide +kernel

theorem c21265fix : c8FixK (cs.L.getD 0 []) (cs.L.getD 1 []) = true := by
  decide +kernel

theorem c21265restr : c8RestrK (cs.L.getD 0 []) (cs.L.getD 1 []) (c8R c8c.Q) cs.L 0 = true := by
  decide +kernel

theorem c21265irr : c8IrrK (cs.L.getD 0 []) c8c.Q = true := by
  decide +kernel

theorem c21265rig : c8RigK (cs.L.getD 0 []) c8c.S = true := by
  decide +kernel

theorem c21265rig2 : c8Rig2K (cs.L.getD 0 []) cs.L = true := by
  decide +kernel


end CertificateChecks.KernelSmithEK
