module

public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalElementary

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_vectors_of_reflection_list :
    ∀ l : List (TauCeti.QuadraticMap.orthogonalGroup Q),
      (∀ r ∈ l, ∃ (v : V) (_ : Invertible (Q v)),
        TauCeti.QuadraticMap.reflectionOrthogonal Q v = r) →
      ∃ lv : List V, lv.length = l.length ∧ (∀ v ∈ lv, Q v ≠ 0) ∧
        ((l.prod : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V) =
          (lv.map (reflect Q)).prod
  | [], _ => ⟨[], rfl, by simp, by simp⟩
  | r :: l, h => by
    obtain ⟨v, hinv, hv⟩ := h r List.mem_cons_self
    obtain ⟨lv, hlen, hQ, hprod⟩ := exists_vectors_of_reflection_list l
      fun r' hr' => h r' (List.mem_cons_of_mem r hr')
    refine ⟨v :: lv, by simp [hlen], fun w hw => ?_, ?_⟩
    · rcases List.mem_cons.1 hw with rfl | hw
      · exact (isUnit_of_invertible (Q w)).ne_zero
      · exact hQ w hw
    · rw [List.prod_cons, Subgroup.coe_mul, hprod, ← hv,
        TauCeti.QuadraticMap.coe_reflectionOrthogonal, ← reflect_eq_reflection]
      simp

theorem orthogonal_odd_reflection_generation [FiniteDimensional K V] (hK : ringChar K ≠ 2)
    (hQ : (polarBilin Q).Nondegenerate) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    ∃ l : List V, l.length ≤ 2 * finrank K V ∧ (∀ v ∈ l, Q v ≠ 0) ∧
      g = (l.map (reflect Q)).prod := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : NeZero (2 : K) := ⟨h2⟩
  let _ : Invertible (2 : K) := invertibleOfNonzero h2
  have hQ' : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  obtain ⟨l, hl, hlen, hprod⟩ :=
    TauCeti.QuadraticMap.exists_reflectionOrthogonal_list_prod_eq Q hQ' ⟨g, hg⟩
  obtain ⟨lv, hlv, hQv, hlvprod⟩ := exists_vectors_of_reflection_list l hl
  refine ⟨lv, by omega, hQv, ?_⟩
  rw [← hlvprod, hprod]

theorem orthogonal_odd_derived_elementary [FiniteDimensional K V] (hK : ringChar K ≠ 2)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      orthElementaryGroup Q := by
  obtain ⟨T, hT3, hTs⟩ := hT
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_hypPairs hQ (T := T) hT3.ge hTs
  exact commutator_orthogonalGroup_eq_elementaryGroup_of_two_ne_zero (Ring.two_ne_zero hK) hQ
    h₁₂ h₁₃ h₂₃


end CFSG.LocalAnalysis.ComponentInitial
