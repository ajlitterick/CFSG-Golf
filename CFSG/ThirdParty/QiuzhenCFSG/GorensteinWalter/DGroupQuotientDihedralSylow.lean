module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DGroupQuotientNotTwoGroup
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer

namespace CFSG
end CFSG
open CFSG

/-!
# Dihedral Sylow subgroups from the D-group quotient clause

An `IsDGroup` supplies cyclic-or-dihedral Sylow two-subgroups.  If one were
cyclic, Burnside transfer would give a normal two-complement and hence a
two-group quotient by the odd core, contradicting `IsDGroupQuotient`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩


end CFSG.GorensteinWalter
