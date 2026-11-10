module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverCheck
public import CFSG.Sporadic.FischerOddCore.Fi22QCheckInputs
public import Certificates.Data.CFSGNative.ONSchreier.Tools
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22QCheckInputs
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore.Native


@[expose] def fi22GoodFix (f : Nat) : Bool := f == 694 || f == 360 || f == 64


end CFSG.Sporadic.FischerOddCore
