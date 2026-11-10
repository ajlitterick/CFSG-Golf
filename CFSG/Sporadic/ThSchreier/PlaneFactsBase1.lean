
module

public import CFSG.Sporadic.ThSchreier.PlaneFactsBase
import all CFSG.Sporadic.ThSchreier.PlaneFactsBase

public import CFSG.Sporadic.ThSchreier.GlobalIndexBase1
public import Certificates.Certificate2317
public meta import CFSG.Sporadic.ThSchreier.Text
public meta import CFSG.Sporadic.ThSchreier.Row
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public meta import Certificates.Data.CFSGNative.Th.Base
public meta import CFSG.Sporadic.ThSchreier.CentralizerData
public meta import CFSG.Sporadic.ThSchreier.WordsBase1
public import CFSG.Sporadic.ThSchreier.CentralizerData

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise


theorem centImage_length : centImageIdx.length = 120 :=
  ctuc_Th_centralizer_plane_data.2.2.2.2.2.2.1


private theorem native_star_mem : 120754 ∈ centImageIdx :=
  Certificates.certificate2317

section Facts


end Facts

end CFSG.Sporadic.ThSchreier
