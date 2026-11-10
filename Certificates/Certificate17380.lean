module

public import Certificates.Kernel.SporSch.HN.C17380

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.HNSchreier in
theorem certificate17380 : ∃ R : Subgroup JH, R ≤ CJ (sJ 2) ∧ Nat.card R = 243 ∧
    (∀ g ∈ CJ (sJ 2), ∀ r ∈ R, g * r * g⁻¹ ∈ R) ∧
    CJ (sJ 2) ⊓ Subgroup.centralizer (R : Set JH) ≤ R :=
  KernelSporSch.HN17380.facts17380

end Certificates
