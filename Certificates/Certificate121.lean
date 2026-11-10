module

public import CFSG.LieType.Steinberg.Adjoint.CertPinnedInputs

public section


open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
open CFSG.Blueprint.Chevalley

public section

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

namespace CertificateChecks.Batch121

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley

namespace AdjData

variable {τ : Tag} (D : AdjData τ)

end AdjData

private theorem f4Data_checkPinned : f4Data.checkPinned = true := by decide +kernel
private theorem e8Data_checkPinned : e8Data.checkPinned = true := by decide +kernel

end CertificateChecks.Batch121

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint in
open CFSG.Blueprint.Chevalley in
theorem certificate121 : (f4Data.checkPinned = true)
    ∧ (e8Data.checkPinned = true) := by
  exact ⟨CertificateChecks.Batch121.f4Data_checkPinned, CertificateChecks.Batch121.e8Data_checkPinned⟩

end Certificates
