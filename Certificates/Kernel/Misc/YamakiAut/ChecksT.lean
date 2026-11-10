module

public import Certificates.Data.Kernel.Misc.YamakiAutM
public import Certificates.Kernel.Misc.YamakiRep.Rec
public import Certificates.Kernel.Misc.YamakiAut.RecT
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.YamakiAutM

open CFSG.KD.YamakiRep CFSG.KD.BfsK
open CFSG.KD.Sp62 (ONE)

@[expose] def ta0 : Nat := 23404555692

@[expose] def ta1 : Nat := 49769138805

@[expose] def tb0 : Nat := 36289536172

@[expose] def tb1 : Nat := 28294481781

@[expose] noncomputable def ch550712C (q : Nat) : Bool :=
  autChunkT RH RT ta0 ta1 tb0 tb1 23040 512 q


end CFSG.KD.YamakiAutM

#kc_slices CFSG.KD.YamakiAutM.ch550712K CFSG.KD.YamakiAutM.ch550712C 45

end
