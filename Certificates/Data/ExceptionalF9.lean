module

public meta import Mathlib.Algebra.QuadraticAlgebra.Defs
public meta import Mathlib.Algebra.Field.ZMod
public meta import Mathlib.Data.ZMod.Defs
public meta import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonExceptionalF9

public section

namespace CFSG

namespace Glauberman
namespace Dickson

open QuadraticAlgebra

instance f9_irreducible :
    Fact (∀ r : ZMod 3, r ^ 2 ≠ (-1 : ZMod 3) + 0 * r) := ⟨by decide⟩

instance : Fintype ExceptionalF9 :=
  Fintype.ofEquiv (ZMod 3 × ZMod 3)
    (QuadraticAlgebra.equivProd (-1 : ZMod 3) 0).symm


end Dickson

end Glauberman

end CFSG
