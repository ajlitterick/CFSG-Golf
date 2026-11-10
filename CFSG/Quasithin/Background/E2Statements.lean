module

public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.A1a

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E2


@[expose] def E213ThreeNonsolvable : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : Hyp28 H T M V), CharTwo H →
    ¬ Group.IsSolvable H → qhatOf (autI h.elem H) ≤ ((2 : ℚ) : WithTop ℚ)

@[expose] def E215Nonsolvable : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : Hyp28 H T M V), CharTwo H →
    IsTISetIn V M → ¬ Group.IsSolvable H → qhatOf (autI h.elem H) < ((2 : ℚ) : WithTop ℚ)


end E2

end CFSG.Quasithin
