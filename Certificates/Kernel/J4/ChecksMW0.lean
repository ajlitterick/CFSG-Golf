module

public import Certificates.Kernel.J4.Data

public section

namespace CertificateChecks.KernelBounds.J4

open CFSG.KJ4.R CFSG.KJ4.RUN CFSG.KJ4.S


theorem mw1 : Nat.beq (runM md kd MW1 (nat_lit 8589934992)) (nat_lit 12884902688) = true := by quickRfl

theorem mw2 : Nat.beq (runM md kd MW2 (nat_lit 12884902688)) (nat_lit 12884903088) = true := by quickRfl


end CertificateChecks.KernelBounds.J4

end
