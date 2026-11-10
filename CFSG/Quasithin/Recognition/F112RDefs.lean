module

public import CFSG.Quasithin.EmptyFaithful.S1422Elim
public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.EmptyFaithful.S1421Surv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique


@[expose] def F112R2bStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M Y H : Subgroup G), Setting1422 T M Y H →
    (Nonempty (oTwoQuot ↥H ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥H ≃* ↥(Sz 0))) →
    CaseTits H (Y ⊔ T) ∨ Case2F4 H (Y ⊔ T)

end CFSG.Quasithin
