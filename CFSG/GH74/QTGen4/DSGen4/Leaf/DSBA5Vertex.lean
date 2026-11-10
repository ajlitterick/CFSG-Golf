module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers
public import CFSG.Quasithin.EmptyFaithful.S1421QA24Borel

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

namespace DSBA5


theorem le_of_sup_dsFrattini_eq {G : Type} [Group G] [Finite G] {Q M : Subgroup G}
    (hM : M ≤ Q) (h : M ⊔ dsFrattini Q = Q) : Q ≤ M := by
  have hA : M.subgroupOf Q ⊔ frattini ↥Q = ⊤ := by
    apply Subgroup.map_injective (f := Q.subtype) Q.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hM,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact h
  have hAtop : M.subgroupOf Q = ⊤ := frattini_nongenerating hA
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥Q) ∈ M.subgroupOf Q := by
    rw [hAtop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hmem

end DSBA5


end CFSG.GH74.QTGen4.DSGen4
