module

public import CFSG.Quasithin.Background.RonanE611Frat
public import CFSG.Quasithin.Background.RonanE611Exp
public import CFSG.Quasithin.Background.RonanE611Sp4
public import CFSG.Quasithin.Background.RonanE611NH
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.NoLocalQuasisimpleComponent
public import CFSG.Quasithin.Background.RonanE611Clause
public import CFSG.Quasithin.Background.RonanE611X

public section

open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.RonanE611

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E6 CFSG.Quasithin.E6.E68Proof

section Setting

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

structure Setting (M V U L : Subgroup G) : Prop where
  comp : IsComponentIn L (Subgroup.centralizer (U : Set G))
  notM : ¬ L ≤ M
  cv : V ⊓ Subgroup.centralizer (L : Set G) = U
  vn : ∀ v ∈ V, v ∈ Subgroup.normalizer (L : Set G)
  ln : (L.subgroupOf (Subgroup.centralizer (U : Set G))).Normal
  uniq : ∀ K : Subgroup G, IsComponentIn K (Subgroup.centralizer (U : Set G)) → K = L
  nl : ∀ g ∈ M ⊓ Subgroup.normalizer (V : Set G), g ∈ Subgroup.normalizer (U : Set G) →
    g ∈ Subgroup.normalizer (L : Set G)


end Setting

section Assemble


end Assemble

section Borel


end Borel

section Sp4


end Sp4

section Cases


end Cases

end CFSG.Quasithin.RonanE611
