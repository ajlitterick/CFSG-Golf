module

public import Certificates.Kernel.SporSch.HN.T0Data
public import Certificates.Data.Kernel.SporSch.HNT0
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSporSch.HNT0

open CFSG.KD.HNT0 CFSG.KS.HNT0

theorem root : rootK AL DF DFO ZP 343 = true := by quickRfl


#kc_each CertificateChecks.KernelSporSch.HNT0 ch10509d (fun j => subK AL PR DF DFO ZP j) 0 343

theorem eb : ebK AL PR 687 ZP EB ZW = true := by quickRfl


end CertificateChecks.KernelSporSch.HNT0

end
