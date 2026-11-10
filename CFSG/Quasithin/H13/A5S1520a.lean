module

public import CFSG.Quasithin.H13.A5L1
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.H13.A5HBar
public import CFSG.Quasithin.H13.A5S1519

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.LieType.BorelTits

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem V_le_H (h1323 : Input1323Two) {H : Subgroup G} (hH : H ∈ S.Hz) : V ≤ H :=
  (S.hypF91 h1323 hH).V_le_H


end Setting

end CFSG.Quasithin.H13.A5
