module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.Kernel.IrrSylowK
public import CFSG.Sporadic.SmallOddCore.M12IrrInputs
meta import CFSG.Sporadic.SmallOddCore.M12IrrInputs
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.M12Irr

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 24

meta def ids3M : Array (Array Nat) := Array.replicate 3 idM

meta def sM : Array (Array Nat) := m12IrrSylowTbls.toArray.map natArr

meta def siM : Array (Array Nat) := sM.map (CFSG.Monster.B.Co2.Native.invCand 24)

meta def lM : Array (Array Nat) :=
  let g := #[natArr m12A1Tbl, natArr m12B1Tbl, natArr m12SigmaTbl]
  g ++ g.map (CFSG.Monster.B.Co2.Native.invCand 24)

meta def recM : Array (Array Nat) := (bfs (fun j t => conjTab 24 idM sM[j]! t) 3 idM 200).tabs

meta def clM : Array (Array Nat) := (recM.map fun x => (sM ++ siM).map fun g => comp 24 x g).flatten

end CertificateChecks.KernelSpor.M12Irr

#kmulh CertificateChecks.KernelSpor.M12IS 24 5 CertificateChecks.KernelSpor.M12Irr.ids3M
  CertificateChecks.KernelSpor.M12Irr.sM CertificateChecks.KernelSpor.M12Irr.idM 200
#kmisc_packarrs CertificateChecks.KernelSpor.M12ISI CertificateChecks.KernelSpor.M12Irr.siM 5
#kmisc_packarrs CertificateChecks.KernelSpor.M12IL CertificateChecks.KernelSpor.M12Irr.lM 5
#kfind CertificateChecks.KernelSpor.M12ICl CertificateChecks.KernelSpor.M12Irr.recM
  CertificateChecks.KernelSpor.M12Irr.clM

namespace CertificateChecks.KernelSpor.M12Irr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.IrrK
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native


end CertificateChecks.KernelSpor.M12Irr

end
