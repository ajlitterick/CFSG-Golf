module

public import Certificates.Data.Sz8CoverInvolutions

public section

namespace CertificateChecks.KernelMiscCoset.C7262

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.Sz8

set_option maxRecDepth 100000

theorem matCheck_centWords : matCheck centWords = true := by
  decide +kernel

end CertificateChecks.KernelMiscCoset.C7262

end
