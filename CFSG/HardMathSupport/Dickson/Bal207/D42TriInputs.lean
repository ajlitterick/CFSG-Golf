module

public import Certificates.Data.D42Triality
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Inputs
public import CFSG.Quasithin.Recognition.CertU33PresInputs

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.D42Tri

open CFSG.EvenSmallLie.OmegaEight CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.J2Cover
  CFSG.Monster.B.Co2.Native CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42
  CFSG.HardMathSupport.Dickson.Bal207.D42TriData CFSG.Quasithin

@[expose] def tblAt (s : String) (j : ℕ) : Table := hexT 3 360 (360 * j) s

@[expose] def rhoTbl (_ : Unit := ()) : Table := arrTable 360 rhoArr

@[expose] def t2Tbl (_ : Unit := ()) : Table := tblAt repHex 0


@[expose] def k2Tbls (_ : Unit := ()) : List Table := (List.range 2).map (tblAt k2Hex)

@[expose] def l0Tbls (_ : Unit := ()) : List Table := (List.range 5).map (tblAt l0Hex)

@[expose] def omGT (_ : Unit := ()) : Array Table :=
  ((List.range 8).map fun i => arrTable 360 genArrs[i]!).toArray

@[expose] def omGI (_ : Unit := ()) : Array Table :=
  ((List.range 8).map fun i => arrTable 360 (invCand 360 genArrs[i]!)).toArray


@[expose] def rhoClassCheck : Bool :=
  let GT := omGT ()
  let GI := omGI ()
  let R := rhoTbl ()
  let c := conjClosureH 360 GT GI R 14400
  conjTreeOK 360 GT GI R c.1 c.2.1 c.2.2 && hkeysDistinct 360 c.1.toList &&
    decide (14400 ≤ c.1.size)


end CFSG.HardMathSupport.Dickson.Bal207.D42Tri
