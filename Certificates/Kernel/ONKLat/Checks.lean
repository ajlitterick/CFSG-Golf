module

public import Certificates.Kernel.ONKLat.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.ON5.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONKL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.ONSchreier
open CertificateChecks.KernelSpor

theorem ch812105_y5 : yOK 5 y5 (List.getD yPos 0 0) = true := by quickRfl

theorem ch812105_y7 : yOK 7 y7 (List.getD yPos 1 0) = true := by quickRfl


theorem ch812105_t : tOK = true := by quickRfl

theorem ch812105_bind : bindOK = true := by quickRfl


end CertificateChecks.KernelSpor.ONKL

#kon_slices CertificateChecks.KernelSpor.ONKL.c5S 0 20
#kon_slices CertificateChecks.KernelSpor.ONKL.c7S 0 20
#kon_join CertificateChecks.KernelSpor.ONKL.c5All CertificateChecks.KernelSpor.ONKL.c5S 20
#kon_join CertificateChecks.KernelSpor.ONKL.c7All CertificateChecks.KernelSpor.ONKL.c7S 20

end
