module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Std.Data.HashMap

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative

open CFSG.Monster.B.Co2.Native

set_option compiler.extract_closed false


@[expose] def commAtN (n : Nat) (p x : Array Nat) : Bool := allLt n fun i => p[x[i]!]! == x[p[i]!]!


end CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative
