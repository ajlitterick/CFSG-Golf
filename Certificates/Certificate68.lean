module

public import CFSG.LieType.Chevalley.RootOps.Cover
public import CFSG.LieType.Chevalley.RootOps.Data.F4Comm

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch68

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem f4_repsCheck : repsCheck .F4 f4Reps = true := by decide +kernel

private theorem f4_coverCheck : coverCheck .F4 f4Reps f4Cover = true := by decide +kernel

end CertificateChecks.Batch68

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate68 : (repsCheck .F4 f4Reps = true)
    ∧ (coverCheck .F4 f4Reps f4Cover = true) := by
  exact ⟨CertificateChecks.Batch68.f4_repsCheck, CertificateChecks.Batch68.f4_coverCheck⟩

end Certificates
