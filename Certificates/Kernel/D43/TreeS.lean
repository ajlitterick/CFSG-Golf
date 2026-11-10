module

public import Certificates.Data.Kernel.D43.Tree
public import Certificates.Kernel.D43.TreeData
public import Certificates.Kernel.D43.HexG
public import CFSG.Certificates.Kernel.Common.EachStep
public import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelD43

open CFSG.KC.D43 CFSG.KC.Enum


@[expose] noncomputable def treeD43b1 (c : Nat) : Bool :=
  treeChunk GX.F TW TR TQ (nat_lit 9) (nat_lit 46343) (nat_lit 6561) (nat_lit 26571)
    (nat_lit 130812) c

end CertificateChecks.KernelD43

#kc_each_step CertificateChecks.KernelD43.treeD43b1 0 26 1 as CertificateChecks.KernelD43.d43treeb1_

namespace CertificateChecks.KernelD43

open CFSG.KC.D43 CFSG.KC.Enum

#kc_forall_chunks treeB1 (fun c => treeD43b1 c = true) 26 CertificateChecks.KernelD43.d43treeb1_ 1


end CertificateChecks.KernelD43

end
