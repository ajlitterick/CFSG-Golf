module

public import Certificates.Kernel.J4.Data

public section

namespace CertificateChecks.KernelBounds.J4

open CFSG.KJ4.R CFSG.KJ4.RUN CFSG.KJ4.S


theorem kw1 : Nat.beq (runK kd KW1 (nat_lit 8589934742)) (nat_lit 8589934892) = true := by quickRfl


theorem kw3 : Nat.beq (runK kd KW3 (nat_lit 8589935042)) (nat_lit 12884902488) = true := by quickRfl


theorem kw6 : Nat.beq (runK kd KW6 (nat_lit 12884902788)) (nat_lit 17179870234) = true := by quickRfl


end CertificateChecks.KernelBounds.J4

end
