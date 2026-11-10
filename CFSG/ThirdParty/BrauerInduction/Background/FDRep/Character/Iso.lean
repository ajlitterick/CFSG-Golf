module

public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Character.Orthogonality
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.SimpleDecomposition

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Characters determine finite-dimensional representations

Over an algebraically closed field of characteristic zero, two finite-dimensional
representations of a finite group are isomorphic if and only if their characters
are equal.

The proof decomposes both representations into finite biproducts of simple
representations, uses Schur orthogonality to compare the multiplicities of each
simple summand, and then reindexes the resulting biproducts.
-/

open CategoryTheory
open CategoryTheory.Limits

namespace FDRep

universe u v


end FDRep
