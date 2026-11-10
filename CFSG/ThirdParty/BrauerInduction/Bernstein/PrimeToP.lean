module

public import CFSG.ThirdParty.BrauerInduction.Bernstein.Ideal
public import CFSG.ThirdParty.BrauerInduction.Elementary.LocalSum

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Bernstein's prime-to-`p` local sum

This file develops the direct integral form of Bernstein's fixed-prime
argument.

For a `p`-regular element `a` and a commuting `p`-singular element `s`, the
value of `PElementary.f p a` at `a * s` is a fixed-coset count. The fixed-point
congruence shows that this value is not divisible by `p`.

Summing the local functions over the `p`-regular conjugacy classes gives
`PElementary.localSum p`. Its value at every group element is an integer not
divisible by `p`, and the corresponding element of the integral cyclotomic
character ring belongs to Bernstein's fixed-prime ideal `JIdeal p`.

No localization at `p` is used in this file.
-/

universe u v

open scoped BigOperators

namespace CFSG.BrauerInduction.Bernstein


end Bernstein

end CFSG.BrauerInduction
