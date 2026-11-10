module

public import CFSG.Milestones.ASVolI.F48.D43.Field
public import CFSG.Sporadic.ON.VecSpec

public section

namespace CFSG.ASVolI

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.F3.Native CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.ON.Native


section Vec

variable (K : Type*) [Field K]


variable {K}


variable [CharP K 3] (ω : K)


variable (hω : ω ^ 3 = ω + 1)


end Vec


section Ops

variable {K : Type*} [Field K]


variable [CharP K 3] (ω : K) (hω : ω ^ 3 = ω + 1)

attribute [local irreducible] burnsideF48d_colTab in


end Ops

section Real

variable {K : Type*} [Field K] [CharP K 3] (ω : K)


variable (hω : ω ^ 3 = ω + 1)


attribute [local irreducible] burnsideF48d_colTab burnsideF48d_genCol in

end Real


section Inj


end Inj


end CFSG.ASVolI
