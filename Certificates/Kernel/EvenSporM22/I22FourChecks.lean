module

public import Certificates.Data.Kernel.EvenSporM22.I22FourDefs
public import Certificates.Kernel.LocalQT.Cov.C4101
public import Certificates.Kernel.EvenSporM22.I22FourWit
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.I22Four
meta import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.I22Four
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
meta import CFSG.Certificates.CosetTableShort
meta import CFSG.Certificates.NativeSchreierCard
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.Open.Defs

set_option maxRecDepth 400000

namespace CFSG.KD.I22F

open CFSG.EvenSporadicStandard.M22Std

meta def natsM (t : Array UInt32) : Array Nat := t.map UInt32.toNat

meta def invM (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate t.size 0
  for i in [0:t.size] do
    r := r.set! t[i]! i
  return r

meta def alM : Array Nat := natsM (i22fAlpha ())

meta def beM : Array Nat := natsM (i22fBeta ())

meta def alIM : Array Nat := invM alM

meta def beIM : Array Nat := invM beM

meta def zM : Array Nat := Id.run do
  let mut r := Array.range beM.size
  for _ in [0:11] do
    r := r.map fun i => beM[i]!
  return r

end CFSG.KD.I22F

#ks_chars CFSG.KD.I22F.CA CFSG.EvenSporadicStandard.M22Std.i22fAlphaText

#ks_chars CFSG.KD.I22F.CB CFSG.EvenSporadicStandard.M22Std.i22fBetaText

#ks_perm CFSG.KD.I22F.A 15 CFSG.KD.I22F.alM

#ks_perm CFSG.KD.I22F.AI 15 CFSG.KD.I22F.alIM

#ks_perm CFSG.KD.I22F.B 15 CFSG.KD.I22F.beM

#ks_perm CFSG.KD.I22F.BI 15 CFSG.KD.I22F.beIM

#ks_perm CFSG.KD.I22F.Z 15 CFSG.KD.I22F.zM

public section

namespace CFSG.KD.I22F

open CFSG.KC.Enum CFSG.KC.DecText CFSG.KC.LQT.Syl CFSG.KC.I22F CFSG.KD.LQT.C4101


end CFSG.KD.I22F

end
