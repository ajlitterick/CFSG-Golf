module

public import Certificates.Data.Kernel.PermCent.L33AutTwin
public import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.L33A

open CFSG.GH74.KGroups.L33 CFSG.Certificates.Kernel.PkCV.KGrp

#kc_each e27B 0 8

theorem kLen : (elemsC QA).length ≤ 8 * 1404 := by decide +kernel


end CFSG.Certificates.Kernel.PkCV.L33A
