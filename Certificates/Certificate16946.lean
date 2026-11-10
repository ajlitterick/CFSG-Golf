module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveInputs
import Certificates.Kernel.Fi23Five.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi23.Native in
theorem certificate16946 :
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native.fi23FiveOK (orbitData ()) = true := by
  rw [CFSG.KD.Fi23K.orbitData_eq']
  exact KernelFi23Five.five_ok

end Certificates
