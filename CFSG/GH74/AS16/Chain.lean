module

public import CFSG.GH74.AS16.Pairs
public import CFSG.GH74.AS16.J1Id
public import CFSG.GH74.AS16.Standard

public section

namespace CFSG.GH74.AS16

open Subgroup CFSG CFSG.Blueprint

@[expose] def LNormal {G : Type} [Group G] (z : G) (L : Subgroup G) : Prop :=
  (L.subgroupOf (centralizer ({z} : Set G))).Normal


theorem Pair.isQuasisimple {G : Type} [Group G] {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (h : Pair T z L) : IsQuasisimple ↥L :=
  LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.isComp.1) h.isComp.2.1

theorem Pair.mem_centralizer {G : Type} [Group G] {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (h : Pair T z L) : z ∈ centralizer (L : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hl => mem_centralizer_singleton_iff.mp (h.isComp.1 hl)


end CFSG.GH74.AS16
