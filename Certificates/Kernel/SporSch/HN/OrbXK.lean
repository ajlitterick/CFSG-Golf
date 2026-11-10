module

public import Certificates.Kernel.SporSch.HN.GenHNX
public import Certificates.Kernel.SporSch.HN.X.Base
public import Certificates.Kernel.SporSch.HN.X.All
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Sporadic.HNSchreier.Data

public section

set_option maxRecDepth 400000

#kc_repo #kc_nat_items_gz CertificateChecks.KernelSporSch.HNX
  "Certificates/Kernel/SporSch/HN/data/hnx_qg.items.gz" 28746 12855385252245474925 QG
#kss_strlits CertificateChecks.KernelSporSch.HNXRoot CFSG.Sporadic.HNSchreier.Data.rootDigits

namespace CertificateChecks.KernelSporSch.HNXOrb

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS.SporSch CFSG.KD.LgHNX CFSG.KD.OrdHN
open CertificateChecks.KernelSporSch

theorem sum_ok : Nat.beq (sumK HNX.CNT) 1139999 = true := by quickRfl
theorem link_ok : linkK HNX.SGT = true := by quickRfl
theorem root_ok : rootK V0C (HNXRoot.c0 ++ HNXRoot.c1) = true := by quickRfl
theorem basis_ok : qBasisK TX CM3 CFSG.Sporadic.HNSchreier.Data.checkPts.toList HNX.QG = true := by
  quickRfl


end CertificateChecks.KernelSporSch.HNXOrb

end
