module

public import Certificates.Data.Kernel.D43.TreePt
public import Certificates.Kernel.D43.TreeData
public import Certificates.Kernel.D43.HexG
public import CFSG.Certificates.Kernel.Common.EachStep
public import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelD43

open CFSG.KC.D43 CFSG.KC.Enum

@[expose] noncomputable def pt3c (c : Nat) : Bool := ptChunk GX.F TW c

end CertificateChecks.KernelD43

#kc_each_step CertificateChecks.KernelD43.pt3c 0 104 1 as CertificateChecks.KernelD43.d43pt3_

namespace CertificateChecks.KernelD43

#kc_forall_chunks pt3 (fun c => pt3c c = true) 104 CertificateChecks.KernelD43.d43pt3_ 1

open CFSG.KC.D43


end CertificateChecks.KernelD43

end
