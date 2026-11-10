module

public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.StandardType.SporadicShape

@[expose] def sporKRestEval {K : Type} [Group K] (gens : List K) (w : List ℤ) : K :=
  (w.map fun l =>
    if 0 < l then gens.getD (l.toNat - 1) 1 else (gens.getD ((-l).toNat - 1) 1)⁻¹).prod

@[expose] def sporKRestParse (s : String) : List ℤ :=
  (s.splitOn " ").filterMap String.toInt?


end CFSG.StandardType.SporadicShape
