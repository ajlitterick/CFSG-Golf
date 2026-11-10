module

public import Certificates.Kernel.Misc.GL4.S3K
public import Certificates.Kernel.Misc.GL4.S3Small
public import Certificates.Kernel.Misc.GL4.A5Facts
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CertificateChecks.KernelMisc.GL4S3

open Matrix CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GL4 Certificates.A5GL42 Certificates.S3x3GL42
open Certificates.GL4 (GL4)
open CertificateChecks.KernelMisc.GL4EA (EA ea_exact)
open CertificateChecks.KernelMisc.GL4A5 (subspaces_complete subspace_eq stab_of vecOfCode_zero
  det_eq_one subC)


@[expose] def u2 (c : Mat4) (h : c * c = 1) : GL4 := ⟨c, c, h, h⟩


end CertificateChecks.KernelMisc.GL4S3

end
