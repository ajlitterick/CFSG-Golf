module

import all CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.B15P4Repl

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]


theorem exists_cv_mul_of_mem_fixV_Bv [Finite V] {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) (v : V) {w : V} (hw : w ∈ fixV (B1.Bv A v)) :
    ∃ a ∈ A, ∃ u ∈ fixV A, w = B1.cv v a * u := by
  have hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := hA.2.2.1.1
  have hbij : Function.Bijective (B1.Fmap hc v) := by
    refine Function.Injective.bijective_of_nat_card_le (B1.Fmap_injective hc v) ?_
    rw [B1.card_Fmap_domain v, card_fixV_Bv hA v]
  obtain ⟨⟨q, u⟩, hqu⟩ := hbij.2 ⟨w, hw⟩
  have h1 : B1.cv v ((Quotient.out q : ↥A) : MulAut V) * (u : V) = w := congrArg Subtype.val hqu
  exact ⟨((Quotient.out q : ↥A) : MulAut V), (Quotient.out q : ↥A).2, u, u.2, h1.symm⟩


end CFSG.Quasithin
