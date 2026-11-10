module

public import CFSG.ThirdParty.BrauerInduction.Bernstein.Congruence
public import CFSG.ThirdParty.BrauerInduction.Background.LinearAlgebra.IntegerLattice

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Bernstein's global ideal and lattice argument

This file combines the fixed-prime ideals `JIdeal p` into the global ideal
`JGlobalIdeal`.

The global ideal is mapped into the finite free lattice of integer-valued class
functions. Bernstein's prime-power congruences and the lattice local-to-global
criterion then show that the unit belongs to `JGlobalIdeal`.
-/


universe u

namespace CFSG.BrauerInduction.Bernstein


section JGlobalIdeal

/-!
## The global Bernstein span

This section combines the prime-local ideals `JIdeal p` into the global integral
`JGlobalIdeal`

-/


end JGlobalIdeal

section JGlobalLattice


namespace JIdeal


end JIdeal
end JGlobalLattice


end CFSG.BrauerInduction.Bernstein
