module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.WordCheck
public import Certificates.Data.CFSGNative.MonsterB.CosetEnum

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbar

open CFSG.Monster CFSG.Monster.B CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7


@[expose] def basisT (j : ℕ) : Model.Pauli := (false, 2 ^ j, 0)

@[expose] def basisD (j : ℕ) : Model.Pauli := (false, 0, 2 ^ j)


@[expose] def validB (p : Model.Pauli) : Bool := decide (p.2.1 < 4096) && decide (p.2.2 < 4096)

@[expose] def ebarPairs (w : List Native.Gen) (imgT imgD : Array Model.Pauli) :
    List (List Native.Gen × List Native.Gen) :=
  ((List.range 12).map fun j => (Native.Gen.rho (basisT j) :: w, w ++ [Native.Gen.rho imgT[j]!])) ++
    (List.range 12).map fun j => (Native.Gen.rho (basisD j) :: w, w ++ [Native.Gen.rho imgD[j]!])


end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbar
