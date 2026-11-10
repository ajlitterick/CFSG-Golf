module

public import CFSG.LieType.Steinberg.Adjoint.CertE7Inputs

public section


open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
open CFSG.Blueprint.Chevalley

public section

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

namespace CertificateChecks.Batch119

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley

private theorem e7AdjData_checkTables : e7AdjData.checkTables = true := by decide +kernel

private theorem e7AdjData_checkSimple : e7AdjData.checkSimple = true := by decide +kernel

private theorem e7AdjData_checkPairNorm : e7AdjData.checkPairNorm = true := by decide +kernel

private theorem e7AdjData_nR : AdjData.nR .E7 = 126 := by decide +kernel

private theorem e7AdjData_checkPinned : e7AdjData.checkPinned = true := by decide +kernel

end CertificateChecks.Batch119

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint in
open CFSG.Blueprint.Chevalley in
theorem certificate119 : (e7AdjData.checkTables = true)
    ∧ (e7AdjData.checkSimple = true)
    ∧ (e7AdjData.checkPairNorm = true)
    ∧ (AdjData.nR .E7 = 126)
    ∧ (e7AdjData.checkPinned = true) := by
  exact ⟨CertificateChecks.Batch119.e7AdjData_checkTables, CertificateChecks.Batch119.e7AdjData_checkSimple, CertificateChecks.Batch119.e7AdjData_checkPairNorm, CertificateChecks.Batch119.e7AdjData_nR, CertificateChecks.Batch119.e7AdjData_checkPinned⟩

end Certificates
