module

public import Certificates.Kernel.Misc.ArgChars
public import Certificates.Data.Kernel.HeisWordsK
public import Certificates.Data.Kernel.HeisN
public import CFSG.LieType.SeitzGeneration.HeisSmallData5

public section

set_option maxRecDepth 1000000

#kc_arg_chars CertificateChecks.KernelHeis.W9704 CFSG.LieType.SeitzGeneration.HeisSmall.words2_5

namespace CertificateChecks.KernelHeis

open CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisWords CFSG.KC.HeisN

theorem heis5_k :
    (fkP 5).heisN 5 5 rawGens5 words1_5 (decodeL W9704.chars) = true := by
  decide +kernel


end CertificateChecks.KernelHeis
