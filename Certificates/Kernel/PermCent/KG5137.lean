module

public import Certificates.Data.Kernel.PermCent.L216Twin
import CFSG.Certificates.Kernel.PermCent.KGrpCSound

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5137

open CFSG.GH74.Uniqueness.SU.K.R4.L216M CFSG.Certificates.Kernel.PkEnum
  CFSG.Certificates.Kernel.PkCV.L216T

theorem kQP : schP QP = true ∧ orderV QP = 4080 := by constructor <;> decide +kernel


end CFSG.Certificates.Kernel.PkCV.KGrp.K5137
