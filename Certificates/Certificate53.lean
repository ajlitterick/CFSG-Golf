module

public import CFSG.LieType.Chevalley.RootOps.Cover
public import CFSG.LieType.Chevalley.RootOps.Data.E7Comm

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch53

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem e7_repsCheck : repsCheck .E7 e7Reps = true := by decide +kernel

private theorem e7_coverCheck : coverCheck .E7 e7Reps e7Cover = true := by decide +kernel

end CertificateChecks.Batch53

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate53 : (repsCheck .E7 e7Reps = true)
    ∧ (coverCheck .E7 e7Reps e7Cover = true) := by
  exact ⟨CertificateChecks.Batch53.e7_repsCheck, CertificateChecks.Batch53.e7_coverCheck⟩

end Certificates
