module

public import CFSG.Sporadic.HNSchreier.FALocal
public import CFSG.Assembly.Defs
import Certificates.Kernel.SporE81.HN27Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.HNSchreier in
theorem certificate9455 : ∃ (z : JH) (R D : Subgroup JH),
    z ^ 3 = 1 ∧ z ≠ 1 ∧ z ∈ PJ ∧ (∀ q ∈ PJ, q * z = z * q) ∧
    CFSG.Assembly.IsElemAbelian 3 D ∧ 81 ≤ Nat.card D ∧
    R ≤ PJ ∧ Nat.card R * 3 = Nat.card PJ ∧
    ∀ s ∈ R, s ^ 3 = 1 → s ∉ Subgroup.zpowers z →
      ∃ g : JH, g * s * g⁻¹ ∈ D ∧ g * z * g⁻¹ ∈ D := KernelE81.HN27K.hn27_local

end Certificates
