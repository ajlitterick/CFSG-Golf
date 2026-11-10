module

public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentInteraction
public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentJoins

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BadComponentDetection


theorem commutes_with_bad_of_quasisimple {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (hcomponent : TwoComponents.IsTwoComponent component)
    (hquasisimple : IsQuasisimple component) :
    ⁅component, TwoComponents.badSubgroup G⁆ = ⊥ := by
  rw [Subgroup.commutator_comm]
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  apply sSup_le
  intro other hbad
  have hne : other ≠ component := fun heq => hbad.2 (heq.symm ▸ hquasisimple)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (TwoComponentInteraction.commutes_of_quasisimple other component hbad.1 hcomponent hne
      (Or.inr hquasisimple))


theorem subnormal_monotone {G : Type*} [Group G] [Finite G]
    (subgroup : Subgroup G) (hsubnormal : IsSubnormal subgroup ⊤) :
    (TwoComponents.badSubgroup subgroup).map subgroup.subtype ≤ TwoComponents.badSubgroup G := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro component hbad
  apply Subgroup.map_le_iff_le_comap.mp
  apply le_sSup
  refine ⟨TwoComponentTransport.of_subnormal_subgroup subgroup hsubnormal component hbad.1, ?_⟩
  intro hquasisimple
  exact hbad.2 (Components.quasisimple_of_equiv
    (component.equivMapOfInjective subgroup.subtype subgroup.subtype_injective) hquasisimple)


end CFSG.ComponentClassification.BadComponentDetection
