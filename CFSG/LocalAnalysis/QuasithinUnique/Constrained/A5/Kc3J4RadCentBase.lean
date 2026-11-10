
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4RadGlobBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Q

@[expose] public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Sporadic.J4
open scoped commutatorElement


theorem conj_mem_centralizer_of_normalizer {X : Type*} [Group X] {Q : Subgroup X} {n u : X}
    (hn : n ∈ Subgroup.normalizer (Q : Set X)) (hu : u ∈ Subgroup.centralizer (Q : Set X)) :
    n * u * n⁻¹ ∈ Subgroup.centralizer (Q : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hw' : n⁻¹ * w * n ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) w).1 hw
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.1 hu _ hw'
  calc w * (n * u * n⁻¹) = n * ((n⁻¹ * w * n) * u) * n⁻¹ := by group
    _ = n * (u * (n⁻¹ * w * n)) * n⁻¹ := by rw [h1]
    _ = (n * u * n⁻¹) * w := by group

theorem normalizer_le_normalizer_centralizer {X : Type*} [Group X] (Q : Subgroup X) :
    Subgroup.normalizer (Q : Set X) ≤
      Subgroup.normalizer ((Subgroup.centralizer (Q : Set X) : Subgroup X) : Set X) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨fun hu => conj_mem_centralizer_of_normalizer hn hu, fun hu => ?_⟩
  have := conj_mem_centralizer_of_normalizer (inv_mem hn) hu
  simpa [mul_assoc] using this

theorem centralizer_le_normalizer_set {X : Type*} [Group X] (Q : Subgroup X) :
    Subgroup.centralizer (Q : Set X) ≤ Subgroup.normalizer (Q : Set X) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro v
  have hcv : ∀ w ∈ Q, c * w * c⁻¹ = w := by
    intro w hw
    have := Subgroup.mem_centralizer_iff.1 hc w hw
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  constructor
  · intro hv
    rw [hcv v hv]
    exact hv
  · intro hv
    have hw := Subgroup.mem_centralizer_iff.1 (inv_mem hc) (c * v * c⁻¹) hv
    have h3 : v = c * v * c⁻¹ := by
      calc v = c⁻¹ * (c * v * c⁻¹) * c := by group
        _ = (c * v * c⁻¹) * c⁻¹ * c := by rw [← hw]
        _ = c * v * c⁻¹ := by group
    rw [h3]
    exact hv


end CFSG.QuasithinUnique.A5
