module

public import Certificates.Data.CFSGNative.Fi22.Centralizer
public meta import Certificates.Data.CFSGNative.Fi22.Centralizer

@[expose] public section

namespace CFSG.Sporadic.Fi22.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.F3.Native

set_option compiler.extract_closed false

def rank3CfgPts : Array Nat := #[0, 1, 63, 369, 322, 2441, 2488, 3427]

def rank3CfgTab (O : COrbit) (i : Nat) : Table := cTab O (genTables O (-2)) rank3CfgPts[i]!


end CFSG.Sporadic.Fi22.Native
