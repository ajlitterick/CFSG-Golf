module

public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFComp
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Elem

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggSup_card_eq_of_commute {A Z : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ z ∈ Z, a * z = z * a) (hAZ : A ⊓ Z = ⊥) :
    Nat.card ↥(A ⊔ Z) = Nat.card A * Nat.card Z := by
  set φ : A × Z →* G := A.subtype.noncommCoprod Z.subtype (fun a z => hcomm a a.2 z z.2)
  have hφ : ∀ (a : A) (z : Z), φ (a, z) = (a : G) * z := fun _ _ => rfl
  have hrange : φ.range = A ⊔ Z := (MonoidHom.noncommCoprod_range _ _ _).trans
    (by rw [Subgroup.range_subtype, Subgroup.range_subtype])
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, z⟩ h
    rw [hφ] at h
    have ha : (a : G) = (z : G)⁻¹ := eq_inv_of_mul_eq_one_left h
    have ha1 : (a : G) = 1 := by
      have hmem : (a : G) ∈ A ⊓ Z := ⟨a.2, ha ▸ Z.inv_mem z.2⟩
      rw [hAZ] at hmem
      exact hmem
    have hz1 : (z : G) = 1 := by
      rw [ha1, one_mul] at h
      exact h
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hz1)
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]


theorem ggCard_mul_card_le_of_commute {D S Bs : Subgroup G} (hD : D ≤ Bs) (hS : S ≤ Bs)
    (hcomm : ∀ x ∈ D, ∀ y ∈ S, x * y = y * x) (hDS : D ⊓ S = ⊥) :
    Nat.card D * Nat.card S ≤ Nat.card Bs := by
  rw [← ggSup_card_eq_of_commute hcomm hDS]
  exact Subgroup.card_le_of_le (sup_le hD hS)

end Elem

section Components


end Components

section Pairs


end Pairs

section Inputs


end Inputs

end CFSG.StandardType
