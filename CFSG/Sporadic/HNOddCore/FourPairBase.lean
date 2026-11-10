
module

public import CFSG.Sporadic.HNOddCore.FourPairBBase
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
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

@[expose] def pk (g : ℕ) : Perm (Fin 256) := Monster.B.Co2.permOfArr 256 colPerms[g]!

theorem prep_pk
    {g : ℕ} (hg : g < 11) : PRep 256 colPerms[g]! (pk g) := by
  have h := (prep_permOfArr (q_parts.2.2.2.2.2.2.2.2.2.1 g hg).1).1
  rw [pk, permOfArr_eq_of_prep h]
  exact h

end CFSG.Sporadic.HNOddCore
