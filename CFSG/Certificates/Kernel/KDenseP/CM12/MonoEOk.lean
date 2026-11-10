module

public import CFSG.Certificates.Kernel.KDenseP.CM12.MonoTab
public import Certificates.Data.Kernel.KDenseP.MonoBind

public section

#kc_listDispatch CFSG.KD.CM12M keyF key 22

namespace CFSG.KD.CM12ME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.CM12M.keyF k) (CFSG.KD.CM12M.ents k)

end CFSG.KD.CM12ME

end
