module

public import CFSG.LieType.Chevalley.RootOps.Cover
public import CFSG.LieType.Chevalley.RootOps.Data.E6Comm

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch49

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem e6_repsCheck : repsCheck .E6 e6Reps = true := by decide +kernel

private theorem e6_coverCheck : coverCheck .E6 e6Reps e6Cover = true := by decide +kernel

end CertificateChecks.Batch49

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate49 : (repsCheck .E6 e6Reps = true)
    ∧ (coverCheck .E6 e6Reps e6Cover = true) := by
  exact ⟨CertificateChecks.Batch49.e6_repsCheck, CertificateChecks.Batch49.e6_coverCheck⟩

end Certificates
