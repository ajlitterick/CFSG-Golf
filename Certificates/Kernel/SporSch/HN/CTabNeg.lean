module

public import CFSG.Sporadic.HNOddCore.CCheckInputs

public section

namespace CertificateChecks.KernelSporSch.HNCTabNeg

open CFSG.Sporadic.HNOddCore.Native

theorem pos : (cRecStep #[1, 2, 0] #[0, 1, 2] #[0, 0, 2] #[1, 2, 0] #[0, 1, 2] #[0, 1, 2] 1 &&
    cRecStep #[1, 2, 0] #[0, 1, 2] #[0, 0, 2] #[1, 2, 0] #[0, 1, 2] #[0, 1, 2] 2) = true := by
  decide +kernel


end CertificateChecks.KernelSporSch.HNCTabNeg
