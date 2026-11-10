module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.ChainTools
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3Data
public import CFSG.Sporadic.Schreier.RuEnum
public import Certificates.Data.CFSGNative.Co3Schreier.Orbit

public section

namespace CFSG.ClassicalInvolution
namespace J3Proof

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier.Co3.Native CFSG.ClassicalInvolution.J3Data


@[expose] def uLevels : Array Level := rawLevels 20520 uStrong uBase

@[expose] def sLevels : Array Level := rawLevels 20520 sStrong sBase


end J3Proof
end CFSG.ClassicalInvolution
