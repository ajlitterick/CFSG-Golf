module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsLift
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups commutatorElement

section Member

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {z : X}

theorem IsClassicalMember3.exists_quaternion_pair_sq (h : IsClassicalMember3 L z) :
    ∃ x ∈ L, ∃ y ∈ L, x * x = z ∧ y * y = z ∧ x * y * x⁻¹ * y⁻¹ = z := by
  have hodd3 : Odd (Nat.card (ZMod 3)) := odd_natCard_zmod_three
  obtain ⟨e⟩ := h.nonempty_equiv
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore L)) :=
    CFSG.ComponentClassification.OddCore.odd_card L
  set ρ : L →* SL(2, ZMod 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore L)) with hρ
  have hρker : ∀ q : L, ρ q = 1 → q ∈ classicalInvolutionOddCore L := fun q hq =>
    (QuotientGroup.eq_one_iff q).mp (e.injective (by simpa [hρ] using hq))
  set z' : L := ⟨z, h.mem⟩ with hz'
  have hz'2 : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_mk]; exact h.orderOf_eq_two
  have hρz : ρ z' = -1 := by
    have h1 := (orderOf_eq_two_iff_of_equiv_sl2 hodd3 e
      (QuotientGroup.mk' (classicalInvolutionOddCore L) z')).mp (orderOf_mk_oddCore_eq_two hz'2)
    rw [hρ]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [h1, MulEquiv.apply_symm_apply]
  have hLcard : Nat.card L = 24 * Nat.card (classicalInvolutionOddCore L) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore L),
      Nat.card_congr e.toEquiv, natCard_sl2Three]
  have hfac : (Nat.card L).factorization 2 = 3 := by
    have h24 : (24 : ℕ).factorization 2 = 3 := by
      have : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
      rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two]
      simp [Nat.Prime.factorization Nat.prime_three]
    have hm : (Nat.card (classicalInvolutionOddCore L)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hd =>
        (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr hd)
    rw [hLcard, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply, h24, hm]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzp : IsPGroup 2 (Subgroup.zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'2, pow_one])
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup L) = 8 := by
    rw [Sylow.card_eq_multiplicity Q, hfac]
    norm_num
  have hinj : ∀ q ∈ (Q : Subgroup L), ρ q = 1 → q = 1 := by
    intro q hq hρq
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp Q.isPGroup') ⟨q, hq⟩
    rw [Subgroup.orderOf_mk] at hk
    have hodd := odd_orderOf_of_mem_oddCore₃ (hρker q hρq)
    rw [hk] at hodd
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hk0⟩)
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  have hQsub : (Q : Subgroup L).map ρ ≤ sl2ThreeQ := by
    rintro _ ⟨q, hq, rfl⟩
    refine mem_sl2ThreeQ_iff.mpr (sl2Three_pow_four_of_pow_eight _ ?_)
    have h1 : q ^ 8 = 1 := by
      have h2 : (⟨q, hq⟩ : (Q : Subgroup L)) ^ Nat.card (Q : Subgroup L) = 1 := pow_card_eq_one'
      have h3 : q ^ Nat.card (Q : Subgroup L) = 1 := congrArg Subtype.val h2
      rwa [hQcard] at h3
    rw [← map_pow, h1, map_one]
  have hQeq : (Q : Subgroup L).map ρ = sl2ThreeQ := by
    refine Subgroup.eq_of_le_of_card_ge hQsub ?_
    rw [natCard_sl2ThreeQ]
    have hinj' : Function.Injective (ρ.comp (Q : Subgroup L).subtype) := by
      rw [injective_iff_map_eq_one]
      intro q hq
      exact Subtype.ext (hinj q.1 q.2 hq)
    have hrange : (ρ.comp (Q : Subgroup L).subtype).range = (Q : Subgroup L).map ρ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj', Subgroup.card_top,
      hQcard]
  have hQz : z' ∈ (Q : Subgroup L) := hQ (Subgroup.mem_zpowers z')
  have heq : ∀ q ∈ (Q : Subgroup L), ρ q = -1 → q = z' := by
    intro q hq hρq
    have h1 : z'⁻¹ * q = 1 := hinj _ ((Q : Subgroup L).mul_mem ((Q : Subgroup L).inv_mem hQz) hq)
      (by rw [map_mul, map_inv, hρz, hρq]; simp)
    exact (inv_mul_eq_one.mp h1).symm
  have hi₀ : (⟨!![2, 2; 2, 1], by decide⟩ : SL(2, ZMod 3)) ∈ sl2ThreeQ :=
    mem_sl2ThreeQ_iff.mpr (by decide +kernel)
  have hj₀ : (⟨!![2, 1; 1, 1], by decide⟩ : SL(2, ZMod 3)) ∈ sl2ThreeQ :=
    mem_sl2ThreeQ_iff.mpr (by decide +kernel)
  obtain ⟨x, hxQ, hx⟩ := hQeq ▸ hi₀
  obtain ⟨y, hyQ, hy⟩ := hQeq ▸ hj₀
  have hxx : x * x = z' := heq _ ((Q : Subgroup L).mul_mem hxQ hxQ) (by
    rw [map_mul, hx]; decide +kernel)
  have hxy : x * y * x⁻¹ * y⁻¹ = z' := heq _ (by
      exact (Q : Subgroup L).mul_mem ((Q : Subgroup L).mul_mem ((Q : Subgroup L).mul_mem hxQ hyQ)
        ((Q : Subgroup L).inv_mem hxQ)) ((Q : Subgroup L).inv_mem hyQ)) (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hx, hy]; decide +kernel)
  have hyy : y * y = z' := heq _ ((Q : Subgroup L).mul_mem hyQ hyQ) (by
    rw [map_mul, hy]; decide +kernel)
  refine ⟨x, x.2, y, y.2, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val hxx
  · exact congrArg Subtype.val hyy
  · exact congrArg Subtype.val hxy
end Member

end CFSG.ClassicalInvolution.Q3

namespace CFSG.ClassicalInvolution.Q3.Q3Y

section Pair


end Pair

end CFSG.ClassicalInvolution.Q3.Q3Y
