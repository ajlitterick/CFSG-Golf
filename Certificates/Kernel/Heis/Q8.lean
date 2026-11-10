module

public import Certificates.Kernel.Misc.ArgChars
public import Certificates.Data.Kernel.HeisWordsK
public import Certificates.Data.Kernel.OuterN
public import CFSG.LieType.SeitzGeneration.OuterSmallData8

public section

set_option maxRecDepth 1000000

#kc_arg_chars CertificateChecks.KernelHeis.W8 CFSG.LieType.SeitzGeneration.HeisSmall.words2_8

namespace CertificateChecks.KernelHeis

open CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisWords CFSG.KC.HeisN

theorem heis8_k : fk8.heisN 8 8 rawGens8 words1_8 (decodeL W8.chars) = true := by
  decide +kernel


theorem outer8_k : fk8.outerN 8 8 rawGens8 words1_8 (decodeL W8.chars) outerRaw8 = true := by
  decide +kernel


end CertificateChecks.KernelHeis
