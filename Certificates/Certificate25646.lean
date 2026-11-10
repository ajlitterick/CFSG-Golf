module

public import CFSG.Sporadic.FischerOddCore.Fi22Ext
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
import Certificates.Kernel.Sporadic.Fi22.HypCBGlue
import Certificates.Kernel.Sporadic.Fi22.C2068

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.ComponentClassification.M12Cover in
open CFSG.Sporadic.Schreier in
theorem certificate25646 : FourClassesLarge ↥(CFSG.Sporadic.Schreier.centralizerIn fi22R (fi22ExtRep 2)) := KernelSpor.Fi22CB.fourClassesLarge_CR2

end Certificates
