
module

public import CFSG.Sporadic.ThSchreier.OrbitCheck819Base
public import CFSG.Sporadic.ThSchreier.PlaneFactsBase
public meta import CFSG.Sporadic.ThSchreier.TransporterBase
public meta import CFSG.Sporadic.ThSchreier.UASpaceBase
public meta import CFSG.Sporadic.ThSchreier.RowBase
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase
public meta import CFSG.Sporadic.ThSchreier.WordsBase
public meta import CFSG.Sporadic.ThSchreier.LocalDataBase
public meta import Certificates.Data.CFSGNative.Th.Base
public meta import CFSG.Sporadic.ThSchreier.CentralizerDataBase

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

theorem orbTable_getElem {i : ℕ} (hi : i < 819) : orbTable[i]! = orbRows i := by
  rw [getElem!_pos orbTable i (by simp [orbTable, hi])]
  simp [orbTable]

end CFSG.Sporadic.ThSchreier
