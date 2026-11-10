module

public import Certificates.Kernel.Misc.ArgChars
public import Certificates.Data.Kernel.HeisWordsK
public import Certificates.Data.Kernel.HeisN
public import CFSG.LieType.SeitzGeneration.HeisSmallData11
public import CFSG.LieType.SeitzGeneration.HeisSmallData5

public section

set_option maxRecDepth 1000000

#kc_arg_chars CertificateChecks.KernelHeis.W11 CFSG.LieType.SeitzGeneration.HeisSmall.words2_11
#kc_arg_chars CertificateChecks.KernelHeis.W5 CFSG.LieType.SeitzGeneration.HeisSmall.words2_5

namespace CertificateChecks.KernelHeis

open CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisWords CFSG.KC.HeisN

theorem heis11_k :
    (fkP 11).heisN 11 11 rawGens11 words1_11 (decodeL W11.chars) = true := by
  decide +kernel


end CertificateChecks.KernelHeis
