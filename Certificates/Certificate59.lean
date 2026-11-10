module

public import CFSG.LieType.Chevalley.RootOps.Cover
public import CFSG.LieType.Chevalley.RootOps.Data.E8Comm

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch59

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem e8_repsCheck : repsCheck .E8 e8Reps = true := by decide +kernel

private theorem e8_coverCheck : coverCheck .E8 e8Reps e8Cover = true := by decide +kernel

end CertificateChecks.Batch59

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate59 : (repsCheck .E8 e8Reps = true)
    ∧ (coverCheck .E8 e8Reps e8Cover = true) := by
  exact ⟨CertificateChecks.Batch59.e8_repsCheck, CertificateChecks.Batch59.e8_coverCheck⟩

end Certificates
