module

public import Certificates.Data.Kernel.Misc.OmegaSixTI
public import Certificates.Kernel.Misc.OmegaSix.Rec
public import Certificates.Kernel.Misc.OmegaSix.RecO
public import Certificates.Kernel.Misc.OmegaSix.TIGen
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.YamakiRepF CFSG.KD.BfsK
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def ch919010 (q : Nat) : Bool := tiChunk RO ROO TIW 512 q


end CFSG.KD.OmegaSix

#kc_slices CFSG.KD.OmegaSix.ch919010K CFSG.KD.OmegaSix.ch919010 102

end
