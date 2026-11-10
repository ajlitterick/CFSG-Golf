module

public import CFSG.Monster.B.Dyadic.Max2K
import Certificates.Kernel.BabyMonster.Pair.Max2C

public section

namespace Certificates

open CertificateChecks

theorem certificate3048 : CFSG.Monster.B.Dyadic.FactMax2 ∧ CFSG.Monster.B.Dyadic.FactPinned :=
  ⟨KernelBM.Pair.factMax2_of,
    KernelBM.Pair.factPinned⟩

end Certificates
