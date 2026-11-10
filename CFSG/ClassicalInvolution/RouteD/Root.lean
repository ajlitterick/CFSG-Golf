module

public import CFSG.LieType.RootSystem.Parabolic
public import Mathlib.Combinatorics.SimpleGraph.Init

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti

variable {I : Type} [Fintype I] [DecidableEq I]

inductive RRoot (A : Matrix I I ℤ) : (I → ℤ) → Prop
  | simple (i : I) : RRoot A (Pi.single i 1)
  | reflect (i : I) {v : I → ℤ} : RRoot A v → RRoot A (CFSG.LieType.RootSystem.reflection A i v)

theorem RRoot.mem_roots {A : Matrix I I ℤ} (hA : IsFiniteType A) {v : I → ℤ} (h : RRoot A v) :
    v ∈ CFSG.LieType.RootSystem.roots hA ∅ := by
  induction h with
  | simple i => exact Or.inl ⟨1, i, by simp⟩
  | reflect i _ ih =>
    rw [← CFSG.LieType.RootSystem.weylAction_simple hA i]
    exact CFSG.LieType.RootSystem.weylAction_mem_roots hA _ ih


theorem RRoot.comp_equiv {J : Type} [Fintype J] [DecidableEq J] (e : I ≃ J) {A : Matrix I I ℤ}
    {A' : Matrix J J ℤ} (hAA : ∀ x y, A x y = A' (e x) (e y)) {v : J → ℤ} (h : RRoot A' v) :
    RRoot A (v ∘ e) := by
  induction h with
  | simple j =>
    have : (Pi.single j (1 : ℤ) : J → ℤ) ∘ e = Pi.single (e.symm j) 1 := by
      funext x
      simp only [Function.comp, Pi.single_apply, Equiv.eq_symm_apply]
    rw [this]
    exact RRoot.simple _
  | @reflect j v _ ih =>
    have key : (CFSG.LieType.RootSystem.reflection A' j v) ∘ e =
        CFSG.LieType.RootSystem.reflection A (e.symm j) (v ∘ e) := by
      funext x
      rw [CFSG.LieType.RootSystem.reflection_apply, CFSG.LieType.RootSystem.reflection_apply]
      have hsum : ∑ y, A (e.symm j) y * (v ∘ e) y = ∑ z, A' j z * v z := by
        rw [← Equiv.sum_comp e]
        refine Finset.sum_congr rfl fun y _ => ?_
        simp [hAA]
      simp only [Function.comp, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
        Equiv.eq_symm_apply]
      simp only [Function.comp] at hsum
      rw [hsum]
    rw [key]
    exact RRoot.reflect _ ih

end CFSG.ClassicalInvolution.RouteD
