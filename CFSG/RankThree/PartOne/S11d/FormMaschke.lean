module

public import CFSG.RankThree.PartOne.LIT.RankAbstract
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.RankThree.PartOne.LIT

open Module

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

theorem exists_add_of_invariant [FiniteDimensional K V] {r : ℕ} (hrK : (r : K) ≠ 0)
    {x : V ≃ₗ[K] V} (hx : x ^ r = 1) {W : Submodule K V} (hW : ∀ w ∈ W, x w ∈ W) {w : V}
    (hw : w ∈ W) : ∃ f ∈ W ⊓ fixedSpace x, ∃ c ∈ W ⊓ commSpace x, w = f + c := by
  classical
  have hc := isCompl_fixedSpace_commSpace hrK hx
  obtain ⟨f₀, hf₀, c₀, hc₀, hfc⟩ : ∃ f₀ ∈ fixedSpace x, ∃ c₀ ∈ commSpace x, f₀ + c₀ = w := by
    have : w ∈ fixedSpace x ⊔ commSpace x := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    exact Submodule.mem_sup.mp this
  have hxr : (x : V →ₗ[K] V) ^ r = 1 := by
    rw [← coe_pow_eq, hx]
    rfl
  have hpow : ∀ i : ℕ, ((x : V →ₗ[K] V) ^ i) f₀ = f₀ := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ, Module.End.mul_apply]; simpa [mem_fixedSpace.mp hf₀] using ih
  have hNf : (∑ i ∈ Finset.range r, (x : V →ₗ[K] V) ^ i) f₀ = (r : K) • f₀ := by
    rw [LinearMap.sum_apply]
    simp [hpow, Nat.cast_smul_eq_nsmul K]
  have hNc : (∑ i ∈ Finset.range r, (x : V →ₗ[K] V) ^ i) c₀ = 0 := by
    obtain ⟨y, hy⟩ := mem_commSpace.mp hc₀
    have h := geom_sum_mul (x : V →ₗ[K] V) r
    rw [hxr, sub_self] at h
    have h2 := congrArg (fun f : V →ₗ[K] V => f y) h
    rw [← hy]
    simpa using h2
  have hNw : (∑ i ∈ Finset.range r, (x : V →ₗ[K] V) ^ i) w = (r : K) • f₀ := by
    rw [← hfc, map_add, hNf, hNc, add_zero]
  have hxiW : ∀ i : ℕ, ((x : V →ₗ[K] V) ^ i) w ∈ W := by
    intro i
    induction i with
    | zero => simpa using hw
    | succ i ih => rw [pow_succ', Module.End.mul_apply]; exact hW _ ih
  have hNW : (∑ i ∈ Finset.range r, (x : V →ₗ[K] V) ^ i) w ∈ W := by
    rw [LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun i _ => hxiW i
  have hf₀W : f₀ ∈ W := by
    rw [hNw] at hNW
    have := W.smul_mem ((r : K)⁻¹) hNW
    rwa [smul_smul, inv_mul_cancel₀ hrK, one_smul] at this
  have hc₀W : c₀ ∈ W := by
    have : c₀ = w - f₀ := by rw [← hfc]; abel
    rw [this]
    exact W.sub_mem hw hf₀W
  exact ⟨f₀, ⟨hf₀W, hf₀⟩, c₀, ⟨hc₀W, hc₀⟩, hfc.symm⟩


section Sesq

variable {σ : K →+* K}


theorem inf_fixedSpace_orthogonal (B : V →ₗ[K] V →ₛₗ[σ] K) {x : V ≃ₗ[K] V}
    (hx : ∀ u v, B (x u) (x v) = B u v) {f c : V} (hf : f ∈ fixedSpace x)
    (hc : c ∈ commSpace x) : B f c = 0 ∧ B c f = 0 := by
  obtain ⟨y, rfl⟩ := mem_commSpace.mp hc
  have hf' := mem_fixedSpace.mp hf
  have h1 : B f (x y) = B f y := by
    have := hx f y
    rwa [hf'] at this
  have h2 : B (x y) f = B y f := by
    have := hx y f
    rwa [hf'] at this
  refine ⟨?_, ?_⟩
  · rw [map_sub, h1, sub_self]
  · rw [map_sub, LinearMap.sub_apply, h2, sub_self]


end Sesq

end CFSG.RankThree.PartOne.LIT
