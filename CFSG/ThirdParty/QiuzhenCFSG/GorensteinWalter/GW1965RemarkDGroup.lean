module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DGroupQuotientDihedralSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalPComplementQuotientPGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuotientTwoGroupNotNormalizerContainsCPrime

namespace CFSG
end CFSG
open CFSG

/-!
# The D-group characterization in the remark after Proposition 9

This module proves the first assertion in the remark after Proposition 9 of
Gorenstein--Walter Part II.  It is kept below the `GW1965` wrapper so that the
wrapper can import the completed theorem without an import cycle.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩


end CFSG.GorensteinWalter
