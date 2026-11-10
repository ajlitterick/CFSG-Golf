
module

public import CFSG.Sporadic.Co2Schreier.ThirdOrderBase
public import CFSG.Sporadic.Co2Schreier.Chains

public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.Co2Schreier.Text
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.SylowCheck
public meta import CFSG.Sporadic.Co2Schreier.CoreCheck
public meta import CFSG.Sporadic.Co2Cert.FaithfulCheck

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

theorem rep_u :
    Rep 2300 uArr locU :=
  rep_compA (repTuple_s.rep (by rw [sTuple_length]; norm_num))
    (repTuple_s.rep (by rw [sTuple_length]; norm_num))

end CFSG.Sporadic.Co2Schreier
