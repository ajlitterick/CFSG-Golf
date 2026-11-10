module

public import Certificates.Data.ExceptionalF9
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG

namespace Glauberman.Dickson

open Matrix
open QuadraticAlgebra

instance : Fact (Nat.Prime 3) := ⟨by decide⟩


end Glauberman.Dickson

end CFSG
