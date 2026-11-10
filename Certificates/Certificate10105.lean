module

public import CFSG.YGroups.Defs
import Certificates.Kernel.Y442.Bound
public import Mathlib

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups in
theorem certificate10105 : Finite (YGroup 4 4 2) ∧ Nat.card (YGroup 4 4 2) ≤ 7531234255143970327756800 := KernelY442.y442_bound

end Certificates
