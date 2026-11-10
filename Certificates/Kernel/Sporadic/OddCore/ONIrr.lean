module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.Kernel.IrrSylowK
public import CFSG.Sporadic.SmallOddCore.ONIrrInputs
meta import CFSG.Sporadic.SmallOddCore.ONIrrInputs
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONIrr

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 32

meta def ids6M : Array (Array Nat) := Array.replicate 6 idM

meta def sM : Array (Array Nat) := onIrrSylowTbls.toArray.map natArr

meta def siM : Array (Array Nat) := sM.map (CFSG.Monster.B.Co2.Native.invCand 32)

meta def recM : Array (Array Nat) := (bfs (fun j t => conjTab 32 idM sM[j]! t) 6 idM 600).tabs

meta def clM : Array (Array Nat) := (recM.map fun x => (sM ++ siM).map fun g => comp 32 x g).flatten

end CertificateChecks.KernelSpor.ONIrr

#kmulh CertificateChecks.KernelSpor.ONIS 32 6 CertificateChecks.KernelSpor.ONIrr.ids6M
  CertificateChecks.KernelSpor.ONIrr.sM CertificateChecks.KernelSpor.ONIrr.idM 600
#kmisc_packarrs CertificateChecks.KernelSpor.ONISI CertificateChecks.KernelSpor.ONIrr.siM 6
#kfind CertificateChecks.KernelSpor.ONICl CertificateChecks.KernelSpor.ONIrr.recM
  CertificateChecks.KernelSpor.ONIrr.clM

namespace CertificateChecks.KernelSpor.ONIrr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.IrrK
open CFSG.ONSchreier.Data


end CertificateChecks.KernelSpor.ONIrr

end
