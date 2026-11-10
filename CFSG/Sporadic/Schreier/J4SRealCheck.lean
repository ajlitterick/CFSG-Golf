module

public import CFSG.Sporadic.Schreier.J4SRealData
public meta import CFSG.Sporadic.Schreier.J4SRealData
public import CFSG.Sporadic.J4.PrimSpec
public meta import CFSG.Sporadic.J4.PrimSpec
public import Certificates.Certificate2181
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs
public import CFSG.Sporadic.Th.F2Spec
public meta import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.J4

theorem span_check : mulRows 112 spanInvRows spanRows = idRows 112 :=
  Certificates.certificate2181.1


end CFSG.Sporadic.J4Schreier
