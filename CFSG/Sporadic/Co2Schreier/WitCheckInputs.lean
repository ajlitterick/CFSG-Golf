
module

public import CFSG.Sporadic.Co2Schreier.WitText
public import CFSG.Sporadic.Co2Schreier.TextCheckBase
public meta import CFSG.Sporadic.Co2Schreier.WitText
public meta import CFSG.Sporadic.Co2Schreier.TextCheckBase
public meta import CFSG.Sporadic.Co2Schreier.TextCheckInputs

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Binary.Native CFSG.Sporadic.Co2Cert


@[expose] def rows22OK (l : List ℕ) : Bool := l.length == 22 && l.all (· < 2 ^ 22)


end CFSG.Sporadic.Co2Schreier
