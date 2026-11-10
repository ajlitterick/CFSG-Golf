module

public import CFSG.Quasithin.H13.ModelsG2Hom
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LieType.Steinberg.G2.Perfect
public import CFSG.Quasithin.Background.G2UAdjoint

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U
open scoped Matrix


variable {K : Type} [Field K]


variable [Finite K]

theorem isSimpleGroup_adjointGroup_G2
    (hK : 3 ≤ Nat.card K) :
    IsSimpleGroup (adjointGroup .G2 K) := by
  have h := (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K hK).2.1
  exact ((QuotientGroup.quotientMulEquivOfEq
    (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup


end CFSG.Quasithin.H13
