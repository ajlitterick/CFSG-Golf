module

public import Certificates.Data.HZ82.Coc24
import CFSG.Certificates.Kernel.Spor.MathieuSound
import Certificates.Kernel.MathieuFam.Checks7227
import Certificates.Data.HZ82.Code22
import CFSG.Holt.SmallGroupsCheck
import CFSG.Quasithin.Background.HMathieuM21Inputs
import Init.Data.Array.Basic
import Init.Data.List.Basic

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Mathieu.Native CFSG.Quasithin.H.Coc24.Native in
theorem certificate7227 : CFSG.Sporadic.Mathieu.Native.check 24 lzData = true ∧ CFSG.Sporadic.Mathieu.Native.check 6 a6colData = true :=
  ⟨CFSG.KS.Mathieu.mcheck_sound (by decide) KernelMathieuFam.lzK,
    CFSG.KS.Mathieu.mcheck_sound (by decide) KernelMathieuFam.a6colK⟩

end Certificates
