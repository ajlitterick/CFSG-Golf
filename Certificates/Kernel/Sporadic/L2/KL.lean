module

public import Certificates.Kernel.Sporadic.L2.Defs2
public import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kon_slices CertificateChecks.KernelSpor.L2K.eltSl 0 3
#kon_slices CertificateChecks.KernelSpor.L2K.nbPSl 0 2
#kon_slices CertificateChecks.KernelSpor.L2K.nbQSl 0 16
#kon_slices CertificateChecks.KernelSpor.L2K.triSl 0 18
#kon_slices CertificateChecks.KernelSpor.L2K.cellK 0 4
#kon_slices CertificateChecks.KernelSpor.L2K.wcSl 0 11
#kon_slices CertificateChecks.KernelSpor.L2K.qSl 0 8
#kon_slices CertificateChecks.KernelSpor.L2K.nb0Q 0 36

#kon_join CertificateChecks.KernelSpor.L2K.eltAll CertificateChecks.KernelSpor.L2K.eltSl 3
#kon_join CertificateChecks.KernelSpor.L2K.nbPAll CertificateChecks.KernelSpor.L2K.nbPSl 2
#kon_join CertificateChecks.KernelSpor.L2K.nbQAll CertificateChecks.KernelSpor.L2K.nbQSl 16
#kon_join CertificateChecks.KernelSpor.L2K.triAll CertificateChecks.KernelSpor.L2K.triSl 18
#kon_join CertificateChecks.KernelSpor.L2K.cellAll CertificateChecks.KernelSpor.L2K.cellK 4
#kon_join CertificateChecks.KernelSpor.L2K.wcAll CertificateChecks.KernelSpor.L2K.wcSl 11
#kon_join CertificateChecks.KernelSpor.L2K.qAll CertificateChecks.KernelSpor.L2K.qSl 8
#kon_join CertificateChecks.KernelSpor.L2K.nb0All CertificateChecks.KernelSpor.L2K.nb0Q 36

namespace CertificateChecks.KernelSpor.L2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.FpBfs

theorem kNbP : nbPK = true := by quickRfl
theorem kNbQ : nbQK = true := by quickRfl
theorem kLoc : locK = true := by quickRfl
theorem kTriR : triRK = true := by quickRfl
theorem kTriL : triLK = true := by quickRfl
theorem kBasic : basicK = true := by quickRfl
theorem kClass : classK = true := by quickRfl
theorem kGroup : groupK = true := by quickRfl
theorem kSortA : sortK 2835 fA ordA posA = true := by quickRfl
theorem kSortT : sortK 486 fT ordT posT = true := by quickRfl


end CertificateChecks.KernelSpor.L2K

end
