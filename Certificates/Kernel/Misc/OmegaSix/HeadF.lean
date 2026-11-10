module

public import Certificates.Data.Foote82OmegaSixAut
public import Certificates.Data.Kernel.Misc.OmegaSixF
public import Certificates.Kernel.Misc.OmegaSix.Rec
public import Certificates.Kernel.Misc.OmegaSix.RecO
public import Certificates.Kernel.Misc.OmegaSix.RecF
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.OmegaSix

open CFSG.CGT.Foote82.OmegaSix CFSG.KD.YamakiRep CFSG.KD.YamakiRepF

theorem fHdr : hdrO RCF (ROO 0) (ROO 1) (ROO 2) (RO 1) = true := by quickRfl

theorem fHead : headC3 RCF 5 5184 = true := by quickRfl

@[expose] noncomputable def ch919150O (q : Nat) : Bool := chunkF3 RCF (cjO ROO RCF) 5 5184 512 q

theorem fPW : pwOK ROO 3 51840 (RO 0) (RO 1) PWF 10 = true := by quickRfl


end CFSG.KD.OmegaSix

#kc_slices CFSG.KD.OmegaSix.ch919150OK CFSG.KD.OmegaSix.ch919150O 11

end
