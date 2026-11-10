module

public import Certificates.Kernel.TitsN12.Walk
public import CFSG.Certificates.Kernel.TitsN12Sound
public import Certificates.Kernel.SporSch.Tits.Inv2266
public import Certificates.Kernel.TitsOct.Glue
import CFSG.Certificates.Kernel.Spor.RawSiftK
public import Certificates.Certificate7050Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsN12

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon
open CertificateChecks.KernelSporSch.TitsHelp
open CFSG.KC.TitsN12K CFSG.KC.TitsN12Sound
open scoped Pointwise


section Congr


end Congr


end CertificateChecks.KernelTitsN12

end
