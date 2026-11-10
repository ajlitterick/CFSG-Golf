module

public import CFSG.Sporadic.Schreier.Co3Cert
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.Schreier.Co3Cert
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Schreier.Co3OrderCheckInputs
public import Certificates.Certificate2158

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native

theorem co3Order_check :
    rawChainOK 276 (co3ChainArrs.extract 0 co3ChainGenCount) co3ChainArrs co3ChainBaseArr
      (wordsArr co3ChainGenCount co3ChainStrongCount co3ChainDerivations) 4 = true ∧
    rawOrbitSizes 276 co3ChainArrs co3ChainBaseArr = [276, 275, 112, 81, 20, 18, 2] ∧
    ((rawLevels 276 co3ChainArrs co3ChainBaseArr)[0]!).pts.size = 276 :=
  Certificates.certificate2158.1


end CFSG.Sporadic.Schreier.Co3
