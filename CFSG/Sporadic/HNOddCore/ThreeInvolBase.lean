
module

public import CFSG.Sporadic.HNOddCore.InvRow2Base
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public meta import CFSG.Sporadic.HNSchreier.RankCheck
public meta import CFSG.Sporadic.HNOddCore.RankData
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
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

@[expose] def c4W (j : Fin 9) : JH := hWordJ InvData.c4Words[(j : ℕ)]!

@[expose] def c6W (j : Fin 10) : JH := hWordJ InvData.c6Words[(j : ℕ)]!

theorem t1R_eq : t1R = cR := rfl

end CFSG.Sporadic.HNOddCore
