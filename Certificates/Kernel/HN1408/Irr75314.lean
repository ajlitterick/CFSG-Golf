module

public import Certificates.Kernel.HN1408.SylS
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.E64Data
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.AData
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckDefs
meta import CFSG.Certificates.CosetTableShort
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.Open.Defs

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Ir75314M

open CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.HNRecog
  CFSG.EvenSporadicStandard.HNRecog.HaradaModel

meta def tabN (t : CFSG.Sporadic.Th.Native.Table) : Array Nat := t.map UInt32.toNat
meta def idM : Array Nat := idTab 1408
meta def wM (w : List Nat) : Array Nat := tabN (tabW w)
meta def genM : Array (Array Nat) := (sWords.map wM).toArray
meta def idsM : Array (Array Nat) := Array.replicate 5 idM
meta def recM : Array (Array Nat) :=
  (bfs (fun j t => conjTab 1408 genM[j]! idsM[j]! t) 5 idM 4096).tabs

meta def qsM : Array (Array Nat) := Id.run do
  let rec_ := recM
  let n := rec_.size
  let keyOf : Array Nat → Nat := fun t => t.getD 2 0 * 1408 + t.getD 0 0
  let kidx : Std.HashMap Nat Nat :=
    (List.range n).foldl (fun m i => m.insert (keyOf (rec_.getD i #[])) i) {}
  let mulI : Nat → Nat → Nat := fun i j =>
    let ti := rec_.getD i #[]
    let tj := rec_.getD j #[]
    kidx.getD (ti.getD (tj.getD 2 0) 0 * 1408 + ti.getD (tj.getD 0 0) 0) 100000
  let aI := kidx.getD (keyOf (wM wordA)) 100000
  let zI := kidx.getD (keyOf (wM wordZ)) 100000
  let azI := mulI aI zI
  let cond : Nat → Bool := fun i =>
    (mulI i i == 0 || mulI i i == aI) && !([0, aI, zI, azI].contains i)
  let inner : Nat → Bool := fun b => (rec_.getD b #[]).getD 0 0 < 704
  let invs := (Array.range n).filter fun b => b != 0 && mulI b b == 0
  let cand := invs.filter inner
  let outer := invs.filter fun b => !inner b
  let row : Nat → Nat → Bool := fun i b => mulI b i == mulI i b &&
    !([0, aI, zI, azI, i, mulI aI i, mulI zI i, mulI azI i].contains b)
  let bx := (Array.range n).map fun i =>
    if cond i then (cand.find? (row i)).getD 4095 else 0
  let b1 := (cand.find? cond).getD 4095
  let mut out : Nat × Nat := (4095, 4095)
  for i in [0:n] do
    if out.1 == 4095 && cond i then
      match outer.find? (row i) with
      | some o => out := (i, o)
      | none => pure ()
  return (bx ++ #[b1, out.1, out.2]).map fun i => rec_.getD i #[]

end CFSG.KD.HN1408.Ir75314M

open CFSG.KD.HN1408.Ir75314M in
#kfind CFSG.KD.HN1408.Ir75314.BX recM qsM

public section

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.BaseMask


end CFSG.KD.HN1408

end
