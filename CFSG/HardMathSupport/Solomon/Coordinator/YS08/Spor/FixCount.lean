module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open scoped Pointwise

@[expose] def fixS {G Ω : Type*} [Group G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω] (g : G) :
    Finset Ω := Finset.univ.filter fun i => g • i = i

theorem mem_fixS {G Ω : Type*} [Group G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω]
    {g : G} {i : Ω} : i ∈ (fixS g : Finset Ω) ↔ g • i = i := by simp [fixS]

section General

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω]

theorem card_fixS_conj (c g : G) :
    (fixS (c * g * c⁻¹) : Finset Ω).card = (fixS g : Finset Ω).card := by
  refine Finset.card_bij (fun i _ => c⁻¹ • i) ?_ ?_ ?_
  · intro i hi
    rw [mem_fixS] at hi ⊢
    have h1 : ((c * g * c⁻¹) • i) = i := hi
    have h2 : c • g • c⁻¹ • i = i := by simpa [mul_smul] using h1
    calc g • c⁻¹ • i = c⁻¹ • (c • g • c⁻¹ • i) := (inv_smul_smul c _).symm
      _ = c⁻¹ • i := by rw [h2]
  · intro i _ j _ h
    simpa using h
  · intro j hj
    refine ⟨c • j, ?_, by simp⟩
    rw [mem_fixS] at hj ⊢
    have : ((c * g * c⁻¹) • c • j) = c • j := by
      calc ((c * g * c⁻¹) • c • j) = c • g • j := by simp [mul_smul]
        _ = c • j := by rw [hj]
    exact this

theorem card_fixS_conj_inv (g x : G) :
    (fixS (g⁻¹ * x * g) : Finset Ω).card = (fixS x : Finset Ω).card := by
  have := card_fixS_conj (Ω := Ω) g⁻¹ x
  rwa [inv_inv] at this


end General

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
