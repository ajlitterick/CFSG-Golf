module

public import Certificates.Kernel.SporSch.HN.T0

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.UniquenessCase.UC22.F10.HNRank in
theorem certificate10509 : HNT0Facts :=
  KernelSporSch.HNT0.facts

end Certificates
