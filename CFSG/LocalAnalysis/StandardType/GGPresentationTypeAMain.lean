module

public import CFSG.LocalAnalysis.StandardType.GGPresentationTypeA
public import CFSG.LieType.CurtisTits.SpecialLinear

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits SpecialLinear
  CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem two_eq_zero_of_card {F : Type} [Field F] [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hf : 1 ≤ f) : (2 : F) = 0 := by
  have := Fintype.ofFinite F
  have h := FiniteField.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, hF] at h
  push_cast at h
  exact (pow_eq_zero_iff (by omega)).mp h


end CFSG.StandardType
