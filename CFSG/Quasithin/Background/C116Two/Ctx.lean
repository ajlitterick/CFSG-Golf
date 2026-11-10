module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Block

public section

namespace CFSG.Quasithin.C116Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Ctx (H T V L : Subgroup G) : Prop where
  charTwo : CharTwo H
  red : IsTwoReducedIn H V
  sylow : IsSylowTwoOf T H
  chi : IsChiBlock H L
  notCent : ¬ L ≤ Subgroup.centralizer (V : Set G)


theorem mem_omegaOneCenter_of_centralizes {T V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVT : V ≤ T) {u : G} (hu : u ∈ V) (hJu : ∀ j ∈ thompsonJ T, j * u = u * j) :
    u ∈ omegaOneCenterOf (thompsonJ T) := by
  rw [← (omegaOne_centralizer_thompsonJ T).1]
  refine Subgroup.subset_closure ⟨⟨hVT hu, Subgroup.mem_centralizer_iff.mpr ?_⟩, hV.2 u hu⟩
  intro j hj
  exact hJu j hj


end CFSG.Quasithin.C116Two
