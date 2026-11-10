module

public import CFSG.Quasithin.Vol2.Ch11SecBHBOne
public import CFSG.Quasithin.Vol2.Ch11SecBDerived
public import CFSG.Quasithin.Vol2.Ch1Prop121
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore
public import CFSG.Quasithin.Vol2.Ch11SecBHBBorel

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_kerIn_of_le_normalizer {N X H : Subgroup G} (hNX : N ≤ X)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) : N ≤ kerIn X H := by
  intro x hx
  show ∀ b ∈ H, b * x * b⁻¹ ∈ X
  intro b hb
  exact hNX ((Subgroup.mem_normalizer_iff.mp (hHN hb) x).mp hx)

omit [Finite G] in
theorem mem_normalizer_sup_of_mem {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine mem_normalizer_of_map_conj_eq ?_
  rw [Subgroup.map_sup, map_conj_eq_self_of_mem_normalizer hA,
    map_conj_eq_self_of_mem_normalizer hB]


end CFSG.Quasithin.Vol2.Ch11.SecB
