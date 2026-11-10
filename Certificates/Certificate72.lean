module

public import CFSG.LieType.Chevalley.RootOps.Cover
public import CFSG.LieType.Chevalley.RootOps.Data.G2Comm

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch72

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem g2_repsCheck : repsCheck .G2 g2Reps = true := by decide +kernel

private theorem g2_coverCheck : coverCheck .G2 g2Reps g2Cover = true := by decide +kernel

end CertificateChecks.Batch72

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate72 : (repsCheck .G2 g2Reps = true)
    ∧ (coverCheck .G2 g2Reps g2Cover = true) := by
  exact ⟨CertificateChecks.Batch72.g2_repsCheck, CertificateChecks.Batch72.g2_coverCheck⟩

end Certificates
