module

public import CFSG.Sporadic.Schreier.TitsInvCheckInputs
public import Certificates.Data.TwoF4LieCheck
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import CFSG.Sporadic.Schreier.TitsAbelCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.RuF45Geom
public meta import Certificates.Data.TwoF4LieData
public meta import Certificates.Data.TwoF4LieCheck
import Certificates.Kernel.SchreierFam.T7450
import Certificates.Kernel.Sporadic.Tits.Bind2264
import CFSG.Certificates.Kernel.SchreierFam.EvalWord
import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Spor.SiftRSound

set_option maxRecDepth 400000

namespace CertificateChecks.Batch7450

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelMisc
  CFSG.Sporadic.Schreier.Tits CFSG.TwoF4Lie CFSG.RuF45
  CFSG.Monster.B.Co2.Native CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
  CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelSchreierFam


end CertificateChecks.Batch7450

public section

namespace Certificates

open CertificateChecks


end Certificates
