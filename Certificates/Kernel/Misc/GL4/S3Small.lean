module

public import Certificates.Kernel.Misc.GL4.S3Data
public import Certificates.Data.Kernel.Misc.GL4Grp
public import Certificates.Data.S3x3GL42

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.GL4S3

open Matrix CFSG.KC.Misc.GL4 Certificates.A5GL42 Certificates.S3x3GL42

@[expose] def Irr3C (a b c : Nat) : Prop :=
  ∀ s ∈ subspaceCodes, StabC a s → StabC b s → StabC c s → s = [0] ∨ s = List.range 16

noncomputable instance (a b c : Nat) : Decidable (Irr3C a b c) := by
  unfold Irr3C; infer_instance


end CertificateChecks.KernelMisc.GL4S3

end
