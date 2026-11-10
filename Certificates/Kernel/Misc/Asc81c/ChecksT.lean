module

public import Certificates.Kernel.Misc.Asc81c.Lin
import all Init.Data.Nat.Fold
import all Init.Data.List.Basic
import all Init.Data.Array.Basic
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAsc81c

open CFSG.Quasithin.Asc81c.Pf.Check

#kc_each candL4 0 16

theorem candL3_ok : candL3 = true := by decide +kernel

#kc_each rowL3 0 24


end CertificateChecks.KernelAsc81c

end
