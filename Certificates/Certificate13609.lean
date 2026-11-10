module

public import Certificates.Kernel.SporSch.HN.C13609

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.HNSchreier in
theorem certificate13609 : Nat.card (Subgroup.centralizer ({sJ 2} : Set JH) ⊓
      Subgroup.centralizer ({c3J 6 * c3J 0 * c3J 0} : Set JH) : Subgroup JH) ≤ 30 ∧
    orderOf (c3J 6 * c3J 0 * c3J 0) = 5 :=
  KernelSporSch.HN13609.facts

end Certificates
