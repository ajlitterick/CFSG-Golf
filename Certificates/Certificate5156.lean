module

public import Certificates.Data.GH74IvkCentM12
public meta import Certificates.Data.GH74IvkCentM12
import Certificates.Kernel.GH74.M12Q2F
import CFSG.GH74.Generic.S45.LEvSporGen
import CFSG.Sporadic.SmallOddCore.ClassSimple

public section

namespace Certificates

open CertificateChecks

theorem certificate5156 : IvkCent.m12CentKaOK = true := KernelGH74.M12Q2.m12CentKa_ok

end Certificates
