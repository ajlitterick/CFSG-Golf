module

public import CFSG.ThirdParty.BrauerInduction.Bernstein.Projection
public import CFSG.ThirdParty.BrauerInduction.LinearSpan

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Brauer induction theorem

This file states the principal consequences of Bernstein's proof of Brauer
induction.

The Bernstein construction proves that the unit belongs to `BrauerIdeal`.
Consequently, multiplying the unit by a representation character places every
representation character in `BrauerSpanChar`. The inclusion
`BrauerSpanChar.le_BrauerSpanLin` then expresses it as an integral linear
combination of characters induced from linear characters of Brauer-elementary
subgroups.

The final theorem gives the equivalent virtual-character formulation.
-/

universe u

open BigOperators

namespace CFSG.BrauerInduction


end CFSG.BrauerInduction
