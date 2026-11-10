module

public import Certificates.Data.Kernel.FixBoundK.TrivAut
public import Certificates.Kernel.FixBoundK.TrivData
public import Certificates.Kernel.MonsterB.Perm3018Data

public section

namespace CertificateChecks.KernelFixBoundK.TrivAutK

open CFSG.KC.FixBoundK CFSG.KC.FixBoundK.Triv CertificateChecks.KernelFixBoundK.TrivD

theorem code : codeK = true := by decide +kernel

theorem aut : autK CertificateChecks.Perm3018.GS CertificateChecks.Perm3018.GA = true := by
  decide +kernel

theorem repLen : lenS reps = 2 := by decide +kernel


end CertificateChecks.KernelFixBoundK.TrivAutK

end
