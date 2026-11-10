module

public import CFSG.Quasithin.Background.D36GluedLift

public section

namespace CFSG.Quasithin

open CFSG.Open

@[expose] def L24NaturalSection : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut V)) (U Z : Subgroup V), BinaryNaturalSL H U Z 2 2 →
      rk ↥U = rk ↥Z + 4 ∧
      (∀ R : Subgroup (MulAut V), R ≤ H → IsElemAbelian2 R → rk ↥R ≤ 2) ∧
      ∀ R : Subgroup (MulAut V), R ≤ H → IsElemAbelian2 R → R ≠ ⊥ →
        rk ↥(commModSub U R Z) + 2 ≤ rk ↥U ∧
        ∀ x ∈ commModSub U R Z, ∀ r ∈ R, r ≠ 1 → ∃ z ∈ U, (r z * z⁻¹) * x⁻¹ ∈ Z

section Glued


namespace GluedSwap


end GluedSwap

end Glued

end CFSG.Quasithin
