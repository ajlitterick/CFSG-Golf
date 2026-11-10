module

public import Certificates.Kernel.MonsterB.Rem3069.Data

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMonB.R3069

open CFSG.KC.Rem3069

@[expose] noncomputable def bad (f : Nat → Nat) (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (RT c) (f (RT c)) (Nat.beq c 100)

theorem neg_vec : chunkOK (bad fun x => Nat.xor x (Nat.shiftLeft 1 111888)) 100 = false := by
  decide +kernel


end CertificateChecks.KernelMonB.R3069

end
