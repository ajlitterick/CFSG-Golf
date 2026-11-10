module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneHilbertNinety
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher


theorem pow_apply_eq_of_apply_eq {K : Type*} [Field K] {φ : K ≃+* K} {x : K} (hx : φ x = x)
    (n : ℕ) : (φ ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, show (φ ^ n * φ) x = (φ ^ n) (φ x) from rfl, hx, ih]


variable {r f : ℕ} {K : Type} [Field K]


theorem unitary_norm_apply (h : UnitaryFieldData r f K) (σ : K ≃+* K) (x : K) :
    h.norm (σ x) = σ (h.norm x) := by
  simp only [UnitaryFieldData.norm, map_mul, map_bar_comm]


theorem exists_bar_ringEquiv (h : UnitaryFieldData r f K) :
    ∃ τ : K ≃+* K, (∀ c, τ c = h.bar c) ∧ orderOf τ = 2 ∧ ∀ σ : K ≃+* K, Commute σ τ := by
  let τ : K ≃+* K :=
    { toFun := h.bar
      invFun := h.bar
      left_inv := h.bar_bar
      right_inv := h.bar_bar
      map_mul' := map_mul h.bar
      map_add' := map_add h.bar }
  refine ⟨τ, fun _ => rfl, ?_, fun σ => ?_⟩
  · refine orderOf_eq_prime (RingEquiv.ext fun c => h.bar_bar c) ?_
    intro h1
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    exact hc (congrArg (fun φ : K ≃+* K => φ c) h1)
  · exact RingEquiv.ext fun c => map_bar_comm h σ c


end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
