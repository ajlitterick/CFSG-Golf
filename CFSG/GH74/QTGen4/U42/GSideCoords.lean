module

public import CFSG.GH74.QTGen4.U42.CoordsB
public import CFSG.GH74.QTGen4.U42.CoordsC
public import CFSG.GH74.QTGen4.U42.ElemAb16

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5


section Plain

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem LT_le_normalizer (S : A5.Setting G T L V) : L ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
  sup_le S.frame.L_le S.frame.T_le

theorem V_le_LT (S : A5.Setting G T L V) : V ≤ L ⊔ T := S.reduced.1


def IsCoords (S : A5.Setting G T L V) {R : Subgroup (Equiv.Perm (Fin 5))}
    (e : ↥(L ⊔ T) ≃* Mof R) : Prop :=
  (∀ (v : G) (hv : v ∈ V),
      ((e ⟨v, V_le_LT S hv⟩ : Mof R) : Mc) = SemidirectProduct.inl (S.frame.ψ ⟨v, hv⟩)) ∧
    ∀ m : ↥(L ⊔ T),
      ((e m : Mof R) : Mc).right = S.frame.ρ ⟨(m : G), LT_le_normalizer S m.2⟩

theorem IsCoords.mk {S : A5.Setting G T L V} {R : Subgroup (Equiv.Perm (Fin 5))}
    (e : ↥(L ⊔ T) ≃* Mof R)
    (hV : ∀ (v : G) (hv : v ∈ V),
      ((e ⟨v, V_le_LT S hv⟩ : Mof R) : Mc) = SemidirectProduct.inl (S.frame.ψ ⟨v, hv⟩))
    (hR : ∀ m : ↥(L ⊔ T),
      ((e m : Mof R) : Mc).right = S.frame.ρ ⟨(m : G), LT_le_normalizer S m.2⟩) :
    IsCoords S e := ⟨hV, hR⟩

theorem IsCoords.left {S : A5.Setting G T L V} {R : Subgroup (Equiv.Perm (Fin 5))}
    {e : ↥(L ⊔ T) ≃* Mof R} (he : IsCoords S e) (v : G) (hv : v ∈ V) :
    ((e ⟨v, V_le_LT S hv⟩ : Mof R) : Mc) = SemidirectProduct.inl (S.frame.ψ ⟨v, hv⟩) :=
  he.1 v hv

theorem IsCoords.right {S : A5.Setting G T L V} {R : Subgroup (Equiv.Perm (Fin 5))}
    {e : ↥(L ⊔ T) ≃* Mof R} (he : IsCoords S e) (m : ↥(L ⊔ T)) :
    ((e m : Mof R) : Mc).right = S.frame.ρ ⟨(m : G), LT_le_normalizer S m.2⟩ :=
  he.2 m


end Plain

end CFSG.GH74.QTGen4.U42
