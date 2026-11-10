module

public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup

public section

namespace CFSG.Quasithin.H13.NQTerm

open CFSG Subgroup
open scoped commutatorElement

variable {E : Type} [Group E]


theorem add_le_pRank_of_commute [Finite E] {p : ℕ} (hp : p.Prime) {A B : Subgroup E}
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAp : ∀ x ∈ A, x ^ p = 1)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hBp : ∀ x ∈ B, x ^ p = 1)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hinf : A ⊓ B = ⊥) {a b : ℕ}
    (ha : Nat.card A = p ^ a) (hb : Nat.card B = p ^ b) : a + b ≤ CFSG.pRank p E := by
  let f : A × B →* E :=
    MonoidHom.noncommCoprod A.subtype B.subtype fun x y => hAB x x.2 y y.2
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    change (x : E) * y = 1 at hxy
    have hx : (x : E) ∈ A ⊓ B := by
      refine ⟨x.2, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hxy]
      exact B.inv_mem y.2
    rw [hinf, mem_bot] at hx
    have hy : (y : E) = 1 := by rw [hx, one_mul] at hxy; exact hxy
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (fun u v => ?_) (fun u => ?_) ?_ f hf
    le_top
  · exact Prod.ext (Subtype.ext (hAc _ u.1.2 _ v.1.2)) (Subtype.ext (hBc _ u.2.2 _ v.2.2))
  · exact Prod.ext (Subtype.ext (by simpa using hAp _ u.1.2))
      (Subtype.ext (by simpa using hBp _ u.2.2))
  · rw [Nat.card_prod, ha, hb, pow_add]


end CFSG.Quasithin.H13.NQTerm
