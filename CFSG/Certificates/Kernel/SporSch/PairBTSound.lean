module

public import CFSG.Certificates.Kernel.SporSch.MathieuBTSound
public import Certificates.Data.CFSGNative.PairSchreier.Counts
import CFSG.Certificates.Kernel.SporSch.ChainKZTot
import CFSG.Sporadic.Schreier.PairChain
import CFSG.Sporadic.Schreier.PairCounts
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.KS.SporSch.MBT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MEnum CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.Certificates.Native CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2.Native
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu

@[expose] def ChainS (n w : Nat) (PS PSI LR TR TRI : Nat → Nat) (kS kO nb BP : Nat)
    (S : Array (Array Nat)) (base : Array Nat) (D : List (List Int)) (NS CH : Nat) : Prop :=
  Binds n w PS kS nb BP S base ∧
    headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true ∧
    LevelsOK n w PS PSI LR TR TRI kS nb BP ∧ n ≤ NS * CH ∧
    ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true

@[expose] def condWords (conds : List (List Bool × Nat)) : List (List Nat × Nat) :=
  conds.map fun c => (c.1.map fun b => if b then 1 else 0, c.2)


end CFSG.KS.SporSch.MBT

end
