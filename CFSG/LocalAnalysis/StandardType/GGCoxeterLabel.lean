module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGIntCartan {Γ : Type*} (M : CoxeterMatrix Γ) (C : Matrix Γ Γ ℤ) : Prop :=
  (∀ i, C i i = 2) ∧ ∀ i j, i ≠ j →
    (M i j = 2 ∧ C i j = 0 ∧ C j i = 0) ∨ (M i j = 3 ∧ C i j = -1 ∧ C j i = -1) ∨
      (M i j = 4 ∧ C i j * C j i = 2 ∧ C i j < 0 ∧ C j i < 0) ∨
      (M i j = 6 ∧ C i j * C j i = 3 ∧ C i j < 0 ∧ C j i < 0)

theorem GGIntCartan.eq_zero_symm {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) {a b : Γ} (hab : a ≠ b) (h : C b a = 0) : C a b = 0 := by
  rcases hC.2 a b hab with ⟨-, h1, -⟩ | ⟨-, -, h2⟩ | ⟨-, -, -, h2⟩ | ⟨-, -, -, h2⟩
  · exact h1
  · rw [h] at h2; exact absurd h2 (by norm_num)
  · rw [h] at h2; exact absurd h2 (lt_irrefl 0)
  · rw [h] at h2; exact absurd h2 (lt_irrefl 0)

section Lift

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {Γ : Type*}

theorem isLiftable_reflection_of_intCartan {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) (h : Γ → V) (α : Γ → Module.Dual R V) (hα : ∀ i, α i (h i) = 2)
    (hP : ∀ i j, α i (h j) = (C i j : R)) :
    M.IsLiftable (fun i => reflection (hα i)) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [M.diagonal i, pow_one]
    exact LinearEquiv.ext fun z => involutive_reflection (hα i) z
  · rcases hC.2 i j hij with ⟨hm, h1, h2⟩ | ⟨hm, h1, h2⟩ | ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩
    · rw [hm]
      exact reflection_mul_reflection_pow_two _ _ (by rw [hP, h1, Int.cast_zero])
        (by rw [hP, h2, Int.cast_zero])
    · rw [hm]
      exact reflection_mul_reflection_pow_three _ _ (by rw [hP, hP, h1, h2]; norm_num)
    · rw [hm]
      exact reflection_mul_reflection_pow_four _ _ (by rw [hP, hP, ← Int.cast_mul, h1]; norm_num)
    · rw [hm]
      exact reflection_mul_reflection_pow_six _ _ (by rw [hP, hP, ← Int.cast_mul, h1]; norm_num)

end Lift

section Recognition

variable {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}

theorem ggWeylReflectionGroup_of_lift {Γ : Type} {M : CoxeterMatrix Γ} (hM : GGIsWeylMatrix M)
    (φ : Γ → MulAut ↥Bs) (hφ : M.IsLiftable φ) (hrefl : ∀ i, GGIsReflection p (φ i))
    (hinj : Function.Injective (M.toCoxeterSystem.lift ⟨φ, hφ⟩)) :
    GGWeylReflectionGroup p (Subgroup.closure (Set.range φ)) := by
  set F := M.toCoxeterSystem.lift ⟨φ, hφ⟩ with hF
  have hsimple : ∀ i, F (M.simple i) = φ i := fun i => by
    rw [← CoxeterMatrix.toCoxeterSystem_simple, hF, CoxeterSystem.lift_apply_simple]
  have hrange : F.range = Subgroup.closure (Set.range φ) := by
    rw [MonoidHom.range_eq_map, ← M.toCoxeterSystem.subgroup_closure_range_simple,
      MonoidHom.map_closure, ← Set.range_comp]
    congr 1
  refine ⟨Γ, M, hM, (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange),
    fun i => ?_⟩
  have hval : (((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
      (M.simple i) : ↥(Subgroup.closure (Set.range φ))) : MulAut ↥Bs) = φ i := by
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply,
      hsimple]
  rw [hval]
  exact hrefl i

end Recognition

theorem linearIndependent_of_det_ne_zero {K V Γ : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Fintype Γ] [DecidableEq Γ] (h : Γ → V) (α : Γ → Module.Dual K V)
    (hdet : (Matrix.of fun i j => α i (h j)).det ≠ 0) : LinearIndependent K h := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hv : Matrix.mulVec (Matrix.of fun i j => α i (h j)) g = 0 := by
    ext i
    have hi := congrArg (α i) hg
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hi
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← hi]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  exact fun i => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hv) i


section Main

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}

theorem ggReflection_linearIndependent_of_noTransvection (hp2 : p ≠ 2)
    (hNT : GGNoTransvection p Bs) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {φ ψ : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs)
    (hψ : ψ ∈ ggInduced ⊤ Bs) (hne : φ ≠ ψ) {x y : V} {f g : Module.Dual (ZMod p) V}
    (hfx : f x = 2) (hgy : g y = 2) (hLφ : ggLin (p := p) ι φ = reflection hfx)
    (hLψ : ggLin (p := p) ι ψ = reflection hgy) :
    LinearIndependent (ZMod p) ![x, y] ∧ LinearIndependent (ZMod p) ![f, g] := by
  have : NeZero (2 : ZMod p) := ⟨zmod_two_ne_zero hp2⟩
  rcases linearIndependent_and_or_exists_transvection hfx hgy with hind | ⟨w, θ, hθw, hT⟩
  · exact hind
  · exfalso
    have key : w = 0 ∨ θ = 0 → False := by
      intro h0
      have h1 : ggLin (p := p) ι (φ * ψ) = 1 := by
        refine LinearEquiv.ext fun v => ?_
        rw [map_mul, hLφ, hLψ, hT]
        rcases h0 with rfl | rfl <;> simp
      have h2 : ggLin (p := p) ι (ψ * ψ) = 1 := by
        refine LinearEquiv.ext fun v => ?_
        rw [map_mul, hLψ, LinearEquiv.mul_apply, involutive_reflection hgy v]
        rfl
      have e1 : φ * ψ = 1 := ggLin_injective ι (by rw [h1, map_one])
      have e2 : ψ * ψ = 1 := ggLin_injective ι (by rw [h2, map_one])
      exact hne (by rw [eq_inv_of_mul_eq_one_left e1, inv_eq_of_mul_eq_one_left e2])
    by_cases hw : w = 0
    · exact key (Or.inl hw)
    by_cases hθ : θ = 0
    · exact key (Or.inr hθ)
    exact hNT (φ * ψ) (mul_mem_ggInduced hφ hψ)
      (ggIsTransvection_of_apply ι hw hθ hθw fun v => by rw [map_mul, hLφ, hLψ, hT])

theorem ggReflection_mul_pow_eq_one_iff (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ ψ : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs) (hψ : ψ ∈ ggInduced ⊤ Bs) (hne : φ ≠ ψ)
    {x y : V} {f g : Module.Dual (ZMod p) V} (hfx : f x = 2) (hgy : g y = 2)
    (hLφ : ggLin (p := p) ι φ = reflection hfx) (hLψ : ggLin (p := p) ι ψ = reflection hgy)
    (hu : f y ≠ 0) (hv : g x ≠ 0) (m : ℕ) :
    (φ * ψ) ^ m = 1 ↔
      ggCoxA (ZMod p) m (f y * g x - 2) = 0 ∧ ggCoxB (ZMod p) m (f y * g x - 2) = 0 := by
  obtain ⟨hxy, hfg⟩ := ggReflection_linearIndependent_of_noTransvection hp2 hNT ι hφ hψ hne hfx
    hgy hLφ hLψ
  rw [← reflection_mul_reflection_pow_eq_one_iff_of_ne_zero hfx hgy hxy hfg hu hv m, ← hLφ, ← hLψ,
    ← map_mul, ← map_pow]
  exact ⟨fun h => by rw [h, map_one], fun h => ggLin_injective ι (by rw [h, map_one])⟩


end Main

end CFSG.StandardType
