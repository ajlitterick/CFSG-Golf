module

public import Certificates.Data.Kernel.ONanNormalK
public import Certificates.Kernel.ONanNormal.Data
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CertificateChecks.ONanNormal

open CFSG.OddStandard.ONanRec.B2K CFSG.OddStandard.ONanRec.NK CFSG.KD.ONanNormal

theorem ck6146_shape : shapeK gs ws rs wt = true := by decide +kernel

noncomputable def ch6146c (k : Nat) : Bool := chunkK gs ws ks rs wt k

#kc_each ch6146c 0 16

#kc_forall_chunks ck6146_chunks (fun k => chunkK gs ws ks rs wt k = true) 16
  CertificateChecks.ONanNormal.ch6146c 1


end CertificateChecks.ONanNormal
