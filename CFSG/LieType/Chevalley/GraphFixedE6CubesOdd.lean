module

public import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K]

theorem orbitField_E6_eq_top_of_card {q : ℕ} {σ : K ≃+* K} (hK : Nat.card K = q ^ 2)
    (hσ : ∀ c, σ c = c ^ q) {a : Fin TwistTag.E6.foldedTag.rank}
    (ha : (TwistTag.E6.orbit a).card = 2) : orbitField TwistTag.E6 K σ.toRingHom a = ⊤ := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    have h := hσ 0
    rw [map_zero, pow_zero] at h
    exact zero_ne_one h
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ hq0)
  have : Fintype K := Fintype.ofFinite K
  refine eq_top_iff.2 fun c _ => (mem_orbitField).2 ?_
  rw [ha, pow_two, RingHom.coe_mul, Function.comp_apply]
  change σ (σ c) = c
  rw [hσ, hσ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]


end CFSG.LieType.Chevalley
