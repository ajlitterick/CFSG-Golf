module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreBInterM
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The maximal-overgroup factorization `M = (B ∩ M) E(M)`

After the A₇ layer model is reached, the source derives
`B ∩ M = O(M)` and `M = (B ∩ M) E(M)` (p. 223).  The first equality is
landed as `firstCase_cyclic_B_inter_M_eq_oddCore_of_a7_layer`.  Here we
show that the component layer covers `M / O(M)`: its image is a
nontrivial normal subgroup of the simple quotient `A₇`, hence is the
whole quotient.  The correspondence theorem then gives
`M = O(M) E(M)`, and the odd-core equality turns `O(M)` back into
`B ∩ M`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u


end CFSG.GorensteinWalter
