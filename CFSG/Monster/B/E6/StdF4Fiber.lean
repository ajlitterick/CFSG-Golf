module

public import CFSG.Monster.B.E6.StdF4FiberCore
public import CFSG.Monster.B.E6.StdF4FiberSets

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension (GStar betaGroup parStar parLeft thetaFirst)
open CFSG.LieType.Chevalley.C2E6Overlap (K)
open CFSG.Monster.B.Classical Matrix Module


theorem fibOrbit_eq
    (d : Fin 5) :
    fibOrbit d = SemidirectProduct.inl '' levPoints (repLevel d) := by
  rw [fibOrbit, conjOrbit_parStar_tW, level_fibWord]

theorem exists_mem_fibOrbit
    {x : stdGroup} (hx : x ∈ rootClass) :
    ∃ d : Fin 5, SemidirectProduct.inl x ∈ fibOrbit d := by
  obtain ⟨g, rfl⟩ := (mem_rootClass_iff _).1 hx
  obtain ⟨d, hd⟩ := exists_repLevel g
  exact ⟨d, by rw [fibOrbit_eq, ← hd]; exact ⟨_, rootMap_mem_levPoints g, rfl⟩⟩


end CFSG.Monster.B.E6.StdF4
