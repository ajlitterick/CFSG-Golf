module

public import CFSG.Sporadic.FischerOddCore.Fi22Ext
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
import Certificates.Kernel.Sporadic.Fi22.HypP0Glue
import Certificates.Kernel.Sporadic.Fi22.C2068

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.ComponentClassification.M12Cover in
open CFSG.Sporadic.Schreier in
theorem certificate25641 : FourClassesLarge ↥(CFSG.Sporadic.Schreier.centralizerIn fi22P (fi22ExtRep 0)) :=
  KernelSpor.Fi22P0.fourClassesLarge_C0 _ le_rfl

end Certificates
