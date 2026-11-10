module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSquareFacts
public import CFSG.Sporadic.FischerOddCore.Fi22Ext
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
import Certificates.Kernel.Sporadic.Fi22.Sq26560Glue
import CFSG.Fischer.T46Unitary
import CFSG.Sporadic.FischerOddCore.Fi22AllInv
import Certificates.Certificate25641
import Certificates.Certificate25642
import Certificates.Certificate25643
import Certificates.Certificate25644
import Certificates.Certificate25645
import Certificates.Certificate25646
import Certificates.Kernel.Sporadic.Fi22.C2068

public section

namespace Certificates

open CertificateChecks

theorem certificate26560 : ∃ (S : Subgroup (Equiv.Perm (Fin 3510))) (d : Equiv.Perm (Fin 3510)),
    CFSG.EvenSporadicStandard.Solomon78.SylowSquareFacts
      (CFSG.Sporadic.Schreier.centralizerIn CFSG.Monster.B.Fischer.fi22P
        (CFSG.Sporadic.FischerOddCore.fi22ExtRep 2)) S
      (CFSG.Sporadic.FischerOddCore.fi22ExtRep 2) d :=
  KernelSpor.Fi22Sq26560.sylowSquareFacts

end Certificates
