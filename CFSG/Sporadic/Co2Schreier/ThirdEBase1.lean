
module

public import CFSG.Sporadic.Co2Schreier.ThirdEBase

public import CFSG.Sporadic.Co2Schreier.ThirdOrderBase1
public import CFSG.Sporadic.Co2Schreier.Kernel
public import Certificates.Certificate2062
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.Co2Schreier.Text
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.SylowCheck
public meta import CFSG.Sporadic.Co2Schreier.CoreCheck
public meta import CFSG.Sporadic.Co2Cert.FaithfulCheck
public import Certificates.Certificate2062Base

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert CFSG.Sporadic.RuSchreier
  CFSG.Sporadic.SmallF2.Native

theorem thirdBase_nodup : witRec.third.baseIndices.Nodup :=
  Certificates.certificate2062.1

theorem thirdBase_lt : ∀ x ∈ witRec.third.baseIndices, x < 2300 :=
  Certificates.certificate2062.2

end CFSG.Sporadic.Co2Schreier
