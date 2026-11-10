
module

public import CFSG.Sporadic.HNOddCore.SylBBase
public import CFSG.Sporadic.HNOddCore.LCheckBase
public import CFSG.Sporadic.HNOddCore.WCheckBase
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public meta import CFSG.Sporadic.HNOddCore.XCheckBase
public meta import CFSG.Sporadic.HNOddCore.PCheckBase
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public meta import CFSG.Sporadic.HNOddCore.QCheck
public meta import Std.Data.HashMap
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public meta import Certificates.Data.CFSGNative.Perm.Chain

@[expose] public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.F5.Native Equiv

abbrev gTabs : Array (Array ℕ) :=
  genTabs hnsData.n (natTab (hnsData.orbit ()).alpha) (natTab (hnsData.orbit ()).beta) hStrongArr
    cRec

end CFSG.Sporadic.HNOddCore
