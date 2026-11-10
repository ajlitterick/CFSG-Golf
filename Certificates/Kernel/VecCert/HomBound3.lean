module

public import Certificates.Kernel.VecCert.HomBoundG
public import CFSG.Certificates.Kernel.Spor.Mat3Sound

public section

namespace CertificateChecks.KernelHom3

open CFSG.KC.Ord CFSG.KS.Mat3 CertificateChecks.KernelHomG

theorem layout3 {d f N LO RM CI ONE UP : Nat} (hc : consts3OK d f N LO RM CI ONE UP = true) :
    LayoutSound (Canon3 N) (mat3 d N) (mul3s d N LO CI RM) (valid3 N LO) ONE :=
  ⟨fun _ _ hA hB => mul3s_sound hc hA hB, (one3_sound hc).1, (one3_sound hc).2,
    fun _ h => (valid3_iff (consts3_facts hc).2.2.1).1 h⟩


end CertificateChecks.KernelHom3

end
