
module

public import CFSG.Sporadic.ThSchreier.GlobalDataBase
public import CFSG.Sporadic.Th.SimpleBase
public meta import CFSG.Sporadic.ThSchreier.RowBase
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase
public meta import Certificates.Data.CFSGNative.Th.Base
public import CFSG.Sporadic.Th.LocalBase
public import CFSG.Sporadic.ThSchreier.BFS

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

@[expose] noncomputable def psiSet (S : Set V) : Set RowV := psi '' S

section Facts

variable (hF : OrbitFacts)
include hF

end Facts

section Cert

variable {c : ℕ} (hC : CertFacts c)
include hC

end Cert

end CFSG.Sporadic.ThSchreier
