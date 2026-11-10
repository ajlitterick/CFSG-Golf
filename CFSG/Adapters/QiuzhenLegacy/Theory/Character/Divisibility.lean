module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.ClassFunction
public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

namespace CFSG

namespace Theory.Character

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def classSet (c : ConjClasses G) : Finset G :=
  letI : DecidableEq (ConjClasses G) := Classical.decEq (ConjClasses G)
  Finset.univ.filter fun g : G => ConjClasses.mk g = c


end

end Theory.Character

end CFSG
