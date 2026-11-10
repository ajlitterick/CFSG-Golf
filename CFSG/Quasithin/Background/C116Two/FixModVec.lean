module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.Quasithin.EmptyFaithful.S14111
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.C116Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem conj_mem_of_mem_normalizer {N : Subgroup G} {j : G}
    (hj : j ∈ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ N) : j * x * j⁻¹ ∈ N :=
  (Subgroup.mem_normalizer_iff.mp hj x).mp hx


end CFSG.Quasithin.C116Two
