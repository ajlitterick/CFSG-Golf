module

public import CFSG.Monster.AxisCount.HSIdentAxis
public import CFSG.Monster.AxisCount.CertData
public import CFSG.Monster.AxisCount.SchreierData0
public import CFSG.Monster.AxisCount.SchreierData1
public import CFSG.Monster.AxisCount.SchreierData2

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount.HS

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.B.Short CFSG.Monster.B CFSG.Monster.B.Rep4371

@[expose] def tpw : Bool → List Native.Gen
  | true => [Native.Gen.tau]
  | false => Native.Gen.tauPow 2

@[expose] def uW (i : Fin 12) (k : Nat) : List Native.Gen := (Cert.UW i)[k]!

@[expose] def xW (i : Fin 12) (r : Nat) (ε : Bool) : List Native.Gen :=
  Cert.hW i r ++ tpw ε ++ Cert.kappaW i r ε

@[expose] def so : Fin 12 → SOrbit
  | 0 => sorbit0
  | 1 => sorbit1
  | 2 => sorbit2
  | 3 => sorbit3
  | 4 => sorbit4
  | 5 => sorbit5
  | 6 => sorbit6
  | 7 => sorbit7
  | 8 => sorbit8
  | 9 => sorbit9
  | 10 => sorbit10
  | 11 => sorbit11

@[expose] def hppU (i : Fin 12) (k : Nat) : List Native.Gen := (so i).uHpp[k]!

@[expose] def bbU (i : Fin 12) (k : Nat) : Nat := (so i).uBaby[k]!

@[expose] def eIdx (ε : Bool) : Nat := if ε then 0 else 1

@[expose] def hppL (i : Fin 12) (r : Nat) (ε : Bool) : List Native.Gen :=
  (so i).lHpp[2 * r + eIdx ε]!

@[expose] def bbL (i : Fin 12) (r : Nat) (ε : Bool) : Nat := (so i).lBaby[2 * r + eIdx ε]!

@[expose] noncomputable def vv (i : Fin 12) : SpaceB := wordLin (Cert.gammaW i) aStar


@[expose] def RecSpec (i : Fin 12) (r : Nat) (ε : Bool) : Prop :=
  wordLin (xW i r ε) (vv i) = vv (Cert.tFin i r ε) ∧
    (bbL i r ε < 10 ∧ wordLin (xW i r ε) (wordLin (Cert.gammaW i) aStarMinus) =
      wordLin (hppL i r ε ++ Cert.gammaW (Cert.tFin i r ε))
        (wordLin (babyW (bbL i r ε)) aStarMinus)) ∧
    wordLin (hppL i r ε) aStar = aStar


end CFSG.Monster.AxisCount.HS
