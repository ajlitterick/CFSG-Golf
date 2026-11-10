module

public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenE

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B1Red

theorem mem_stabSub_map_subtype {V : Type*} [CommGroup V] {U : Subgroup V} {h : MulAut V}
    (hU : h ∈ stabSub U) {Ib : Subgroup ↥U} (hI : resHom U ⟨h, hU⟩ ∈ stabSub Ib) :
    h ∈ stabSub (Ib.map U.subtype) := by
  intro v
  constructor
  · intro hv
    have hvU : h v ∈ U := Subgroup.map_subtype_le Ib hv
    have hvU' : v ∈ U := (hU v).1 hvU
    obtain ⟨u, rfl⟩ : ∃ u : ↥U, (u : V) = v := ⟨⟨v, hvU'⟩, rfl⟩
    obtain ⟨u', hu', hu'e⟩ := hv
    have : u' = resHom U ⟨h, hU⟩ u := U.subtype_injective hu'e
    exact ⟨u, (hI u).1 (this ▸ hu'), rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨resHom U ⟨h, hU⟩ u, (hI u).2 hu, rfl⟩

end B1Red


end CFSG.Quasithin
