module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherEscapingRankTwo

public section

namespace CFSG.ProperTwoGeneratedCore.InvolutionCosetFusion

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G]

theorem orderOf_eq_of_isConj {x y : G} (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨c, hc⟩ := h
  exact hc.orderOf_eq


theorem exists_distinct_cosets_of_three_le_relIndex {U V : Subgroup G}
    (hindex : 3 ≤ U.relIndex V) : ∃ x ∈ V, ∃ y ∈ V, x ∉ U ∧ y ∉ U ∧ x⁻¹ * y ∉ U := by
  by_contra hcon
  push Not at hcon
  have hle : U.relIndex V ≤ 2 := by
    rw [Subgroup.relIndex, Subgroup.index]
    by_cases hex : ∃ x ∈ V, x ∉ U
    · obtain ⟨x₀, hx₀V, hx₀U⟩ := hex
      let f : Bool → V ⧸ U.subgroupOf V := fun b =>
        if b then QuotientGroup.mk ⟨x₀, hx₀V⟩ else QuotientGroup.mk 1
      have hf : Function.Surjective f := by
        intro q
        induction q using QuotientGroup.induction_on with
        | H y =>
          by_cases hyU : (y : G) ∈ U
          · refine ⟨false, ?_⟩
            simp only [f, Bool.false_eq_true, ↓reduceIte]
            rw [QuotientGroup.eq]
            simpa [Subgroup.mem_subgroupOf] using hyU
          · refine ⟨true, ?_⟩
            simp only [f, ↓reduceIte]
            rw [QuotientGroup.eq]
            simpa [Subgroup.mem_subgroupOf] using hcon x₀ hx₀V y y.property hx₀U hyU
      calc Nat.card (V ⧸ U.subgroupOf V) ≤ Nat.card Bool := Nat.card_le_card_of_surjective f hf
        _ = 2 := by simp
    · push Not at hex
      have hsub : U.subgroupOf V = ⊤ := by
        rw [eq_top_iff]
        intro y _
        exact Subgroup.mem_subgroupOf.mpr (hex y y.property)
      rw [hsub]
      simp
  omega

theorem transitive_quotient_cosets_exclude_class [Finite G] {u z : G}
    (hu : orderOf u = 2) (hnconj : ¬ IsConj u z)
    (V U : Subgroup G) (hUsq : ∀ x ∈ U, x * x = 1) (hindex : 4 ≤ U.relIndex V)
    (hUz : ∀ w ∈ U, w ≠ 1 → IsConj z w)
    (A : Subgroup G) (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (htrans : ∀ x ∈ V, x ∉ U → ∀ y ∈ V, y ∉ U → ∃ a ∈ A, y⁻¹ * (a * x * a⁻¹) ∈ U)
    (hsat : ∀ x ∈ V, IsConj u x → ∀ w ∈ U, IsConj u (x * w))
    (hprod : ∀ x y : G, IsConj u x → IsConj u y → x ≠ y → Commute x y → IsConj z (x * y)) :
    ∀ x ∈ V, ¬ IsConj u x := by
  intro v hvV hvu
  have hu1 : u ≠ 1 := by
    rintro rfl
    simp at hu
  have huu : u * u = 1 := by simpa only [hu, pow_two] using pow_orderOf_eq_one u
  have hvU : v ∉ U := by
    intro hvU
    have hv1 : v ≠ 1 := by
      rintro rfl
      exact hu1 (isConj_one_right.mp hvu.symm)
    exact hnconj (hvu.trans (hUz v hvU hv1).symm)
  have hVU : ∀ y ∈ V, y ∉ U → IsConj u y := by
    intro y hyV hyU
    obtain ⟨a, haA, hw⟩ := htrans v hvV hvU y hyV hyU
    have haV : a * v * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hAV haA) v).mp hvV
    have hconj : IsConj u (a * v * a⁻¹) := hvu.trans (isConj_iff.mpr ⟨a, rfl⟩)
    have h := hsat _ haV hconj _ (U.inv_mem hw)
    have hy : a * v * a⁻¹ * (y⁻¹ * (a * v * a⁻¹))⁻¹ = y := by group
    rwa [hy] at h
  have hsqV : ∀ x ∈ V, x * x = 1 := by
    intro x hxV
    by_cases hxU : x ∈ U
    · exact hUsq x hxU
    · have hord := (orderOf_eq_of_isConj (hVU x hxV hxU)).symm.trans hu
      simpa only [hord, pow_two] using pow_orderOf_eq_one x
  have hcommV : ∀ x ∈ V, ∀ y ∈ V, Commute x y := by
    intro x hxV y hyV
    have hxy := hsqV (x * y) (V.mul_mem hxV hyV)
    have hx := hsqV x hxV
    have hy := hsqV y hyV
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy
    have : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_left hxy
    rw [mul_inv_rev, hxinv, hyinv] at this
    exact this.symm
  obtain ⟨x, hxV, y, hyV, hxU, hyU, hxyU⟩ := exists_distinct_cosets_of_three_le_relIndex
    (by omega : 3 ≤ U.relIndex V)
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left (hsqV x hxV)
  rw [hxinv] at hxyU
  have hne : x ≠ y := by
    rintro rfl
    exact hxyU (by rw [hsqV x hxV]; exact U.one_mem)
  have hz := hprod x y (hVU x hxV hxU) (hVU y hyV hyU) hne (hcommV x hxV y hyV)
  have hu' := hVU (x * y) (V.mul_mem hxV hyV) hxyU
  exact hnconj (hu'.trans hz.symm)

end CFSG.ProperTwoGeneratedCore.InvolutionCosetFusion
