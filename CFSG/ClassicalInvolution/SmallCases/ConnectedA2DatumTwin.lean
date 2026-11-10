module

public import CFSG.ClassicalInvolution.Omega
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutFrame
public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2FactsKG2Dichotomy
public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.Models.SymplecticPairs

public section

namespace CFSG.ClassicalInvolution.ConnectedA2

open scoped MatrixGroups
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime]

section UniqueInvolution

variable {Y : Type} [Group Y] [Finite Y]

theorem isUniqueInvolution_of_isClassicalMember (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {L : Subgroup Y} {z : Y} (h : IsClassicalMember p f L z) : IsUniqueInvolution L z := by
  have hodd := odd_natCard_galoisField hp2 hq
  obtain ⟨e⟩ := h.nonempty_equiv
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore L)) :=
    CFSG.ComponentClassification.OddCore.odd_card L
  have hzc : ∀ l ∈ L, z * l = l * z := fun l hl =>
    Subgroup.mem_centralizer_iff.mp (isSubnormal_le h.subnormal hl) z (Set.mem_singleton z)
  have hz2 : orderOf z = 2 := h.orderOf_eq_two
  refine ⟨h.mem, ?_, ?_, ?_⟩
  · intro h1
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  · have := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at this
  · intro y hy hy2
    set y' : L := ⟨y, hy⟩ with hy'
    set z' : L := ⟨z, h.mem⟩ with hz'
    have hz'c : ∀ l : L, l * z' = z' * l := fun l => Subtype.ext (hzc l.1 l.2).symm
    have hz'2 : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_mk]; exact hz2
    by_cases hy1 : y' = 1
    · exact Or.inl (congrArg Subtype.val hy1)
    · refine Or.inr ?_
      have hyy : y' * y' = 1 := Subtype.ext hy2
      have hord : orderOf y' = 2 := orderOf_eq_prime (by rwa [pow_two]) hy1
      have hρy := (orderOf_eq_two_iff_of_equiv_sl2 hodd e
        (QuotientGroup.mk' (classicalInvolutionOddCore L) y')).mp
        (orderOf_mk_oddCore_eq_two hord)
      have hρz := (orderOf_eq_two_iff_of_equiv_sl2 hodd e
        (QuotientGroup.mk' (classicalInvolutionOddCore L) z')).mp
        (orderOf_mk_oddCore_eq_two hz'2)
      have hmem : z'⁻¹ * y' ∈ classicalInvolutionOddCore L :=
        QuotientGroup.eq.mp (hρz.trans hρy.symm)
      have hzz : z' * z' = 1 := by
        have := pow_orderOf_eq_one z'
        rwa [hz'2, pow_two] at this
      have hyo : y' = z' * (z'⁻¹ * y') := by group
      set o : L := z'⁻¹ * y' with ho
      have hoo : o * o = 1 := by
        have h1 : (z' * o) * (z' * o) = (z' * z') * (o * o) := by
          calc (z' * o) * (z' * o) = z' * (o * z') * o := by group
            _ = z' * (z' * o) * o := by rw [hz'c o]
            _ = (z' * z') * (o * o) := by group
        rw [← hyo, hyy, hzz, one_mul] at h1
        exact h1.symm
      have ho1 : o = 1 := by
        by_contra ho1
        exact ho1 (eq_one_of_mem_odd_of_orderOf_eq_two_pow hOodd hmem (k := 1)
          (by rw [pow_one]; exact orderOf_eq_prime (by rwa [pow_two]) ho1))
      rw [ho1, mul_one] at hyo
      exact congrArg Subtype.val hyo

end UniqueInvolution

section Twins

variable {G : Type} [Group G]

theorem orderOf_eq_two_of_isUniqueInvolution {K : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) : orderOf z = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one


end Twins

section Tight

variable {G : Type} [Group G] [Finite G]


end Tight

section Inputs

variable (p f)


end Inputs

section Exact

variable {G : Type} [Group G]

theorem oddCore_range_eq_bot {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h4 : 4 ≤ Nat.card F) {φ : SL(2, F) →* G} (hφ : Function.Injective φ) :
    classicalInvolutionOddCore ↥φ.range = ⊥ := by
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  let e : SL(2, F) ≃* φ.range := MonoidHom.ofInjective hφ
  have h := CFSG.ComponentClassification.OddCore.equiv_invariant e
  have hO : componentClassificationOddCore SL(2, F) = ⊥ :=
    CFSG.ClassicalInvolution.ModelFacts.LinearAut.oddCore_sl2_eq_bot h2 h4
  rw [hO, Subgroup.map_bot] at h
  exact h.symm


end Exact

section Connected

variable {G : Type} [Group G]


end Connected

section NoTwins

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]


omit [Finite G] in
theorem exists_third_member {M₁ M₂ K₁ K₂ : Subgroup G} (hM12 : M₁ ≠ M₂)
    (hnc : ¬ Commutes M₁ M₂) (hcom : Commutes K₁ K₂) :
    (M₁ ≠ K₁ ∧ M₁ ≠ K₂) ∨ (M₂ ≠ K₁ ∧ M₂ ≠ K₂) := by
  by_contra hcon
  rw [not_or, not_and_or, not_and_or, not_not, not_not, not_not, not_not] at hcon
  obtain ⟨e1, e2⟩ := hcon
  rcases e1 with rfl | rfl <;> rcases e2 with rfl | rfl
  · exact hM12 rfl
  · exact hnc hcom
  · exact hnc hcom.symm
  · exact hM12 rfl


end NoTwins

section Injective


end Injective

end CFSG.ClassicalInvolution.ConnectedA2
