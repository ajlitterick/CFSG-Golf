module

public import Certificates.Kernel.Sporadic.OddCore.HL
public import Certificates.Kernel.LocalComp.HeFixData
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.LocalCompUnpack
public import CFSG.Sporadic.SmallOddCore.HeldTwoAInputs
meta import CFSG.Sporadic.SmallOddCore.HeldTwoAInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.GroupTheory.LocalCores.Fitting

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.He2286

open CFSG.Sporadic.SmallOddCore

meta def uM : Array (Array Nat) := #[heU105Arr, CFSG.PSL3Four.Native.invTab 105 heU105Arr]

end CertificateChecks.KernelSpor.He2286

#kmisc_packarrs CertificateChecks.KernelSpor.He2286.U CertificateChecks.KernelSpor.He2286.uM 7

namespace CertificateChecks.KernelSpor.He2286

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu CertificateChecks.KernelSpor
open CertificateChecks.KernelLC.HeFix CFSG.Sporadic.SmallOddCore


end CertificateChecks.KernelSpor.He2286

end
