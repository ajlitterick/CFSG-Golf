
module

public import Certificates.Data.Kernel.PermCent.L34MTwin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.L34MT

open CFSG.GH74.Uniqueness.SU.K.R4.L34M CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkEnum


theorem kQP : schP QP = true := by decide +kernel

theorem kCent : ((elemsC QP).filter fun g => eq22C g (cOf rep4) (cOf rep4) g).length % 9 = 0 := by
  decide +kernel


end CFSG.Certificates.Kernel.PkCV.L34MT
