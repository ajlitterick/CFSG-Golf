module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceTypes
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

abbrev F112Conc : Type 1 :=
  ∀ (G : Type) [Group G] [Finite G], Subgroup G → Subgroup G → Subgroup G → Prop


@[expose] def F112SliceExotic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → PairExotic L1 L2 → False


section Ordered

variable {C : F112Conc} (hC : ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
  C G L2 L1 S → C G L1 L2 S)


end Ordered


theorem F112SliceExotic.of_parts
    (hu : ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
      F112Hyp L1 L2 S → VU3two L1 → False)
    (hd : ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
      F112Hyp L1 L2 S → VFD L1 → VFD L2 → False) : F112SliceExotic := by
  intro G _ _ L1 L2 S hh hp
  rcases hp with h | h | ⟨h1, h2⟩
  · exact hu G L1 L2 S hh h
  · exact hu G L2 L1 S hh.symm h
  · exact hd G L1 L2 S hh h1 h2

end CFSG.Quasithin
