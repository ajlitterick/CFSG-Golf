module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeCharData
public import Std.Data.HashSet

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar


@[expose] def castL (vec : List ℕ) : List ℤ := vec.map fun x : ℕ => (x : ℤ)

@[expose] def pairZ (T : RootTables) (k : ℕ) (v : List ℤ) : ℤ := dotL (T.vecs.getD k []) v


end CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular
