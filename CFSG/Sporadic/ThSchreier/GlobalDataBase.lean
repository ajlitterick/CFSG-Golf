
module

public import CFSG.Sporadic.ThSchreier.LocalOrbitBase
public import CFSG.Sporadic.Schreier.LyBFS

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.LySchreier
  Pointwise

noncomputable abbrev planeWSet : Set RowV := (planeW : Set RowV)


end CFSG.Sporadic.ThSchreier
