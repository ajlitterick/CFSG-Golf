module

public import CFSG.Monster.Code.Basis
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.Monster.Code

open Polynomial
open scoped Finset

theorem filter_C : Finset.univ.filter (· ∈ C) =
    Finset.univ.image fun μ : Fin 12 → ZMod 2 => ∑ i, μ i • B i := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    mem_C_iff_exists_comb]

theorem sum_C {M : Type*} [AddCommMonoid M] (F : (Fin 24 → ZMod 2) → M) :
    ∑ x ∈ Finset.univ.filter (· ∈ C), F x = ∑ μ : Fin 12 → ZMod 2, F (∑ i, μ i • B i) := by
  rw [filter_C, Finset.sum_image fun μ _ ν _ h => comb_injective h]

theorem sum_C_eq_treeSumN {M : Type*} [AddCommMonoid M] (F : (Fin 24 → ZMod 2) → M) :
    ∑ x ∈ Finset.univ.filter (· ∈ C), F x = treeSumN (fun a => F (bvec 24 a)) Bmask 12 0 := by
  rw [sum_C, ← sum_comb_bvec 24 F Bmask 12 0, bvec_zero]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [zero_add, B_eq_bvec]

@[expose] def goodWt (w : ℕ) : Bool := w == 0 || w == 8 || w == 12 || w == 16 || w == 24

@[expose] def badCount : ℕ := treeSumN (fun a => if goodWt (popc 24 a) then 0 else 1) Bmask 12 0

@[expose] def wtCount (w : ℕ) : ℕ := treeSumN (fun a => if popc 24 a = w then 1 else 0) Bmask 12 0

theorem badCount_eq : badCount = 0 := by decide +kernel
theorem wtCount_eight : wtCount 8 = 759 := by decide +kernel
theorem wtCount_twelve : wtCount 12 = 2576 := by decide +kernel

theorem card_filter_wt (w : ℕ) :
    #{x ∈ Finset.univ.filter (· ∈ C) | hammingNorm x = w} = wtCount w := by
  rw [Finset.card_filter, sum_C_eq_treeSumN]
  simp only [wtCount, hammingNorm_bvec]

theorem wt_mem {x : Fin 24 → ZMod 2} (hx : x ∈ C) :
    hammingNorm x ∈ ({0, 8, 12, 16, 24} : Finset ℕ) := by
  have h := badCount_eq
  rw [badCount, ← funext fun a => congrArg (fun w => if goodWt w then 0 else 1)
    (hammingNorm_bvec 24 a), ← sum_C_eq_treeSumN (fun x => if goodWt (hammingNorm x) then 0 else 1),
    Finset.sum_eq_zero_iff] at h
  have := h x (Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩)
  simp only [goodWt, Bool.or_eq_true, beq_iff_eq, ite_eq_left_iff, one_ne_zero, imp_false,
    not_not] at this
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

theorem four_dvd_wt {x : Fin 24 → ZMod 2} (hx : x ∈ C) : 4 ∣ hammingNorm x := by
  have := wt_mem hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

theorem eight_le_wt {x : Fin 24 → ZMod 2} (hx : x ∈ C) (h0 : x ≠ 0) : 8 ≤ hammingNorm x := by
  have := wt_mem hx
  have h1 : hammingNorm x ≠ 0 := hammingNorm_ne_zero_iff.2 h0
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

theorem wt_B : ∀ i, hammingNorm (B i) = 8 := by
  intro i; rw [B_eq_bvec, hammingNorm_bvec]; revert i; decide


theorem B_dot_B : ∀ i j, B i ⬝ᵥ B j = 0 := by
  intro i j
  rw [B_eq_bvec, B_eq_bvec, bvec_dotProduct]
  revert i j; decide

theorem dotProduct_eq_zero {x y : Fin 24 → ZMod 2} (hx : x ∈ C) (hy : y ∈ C) : x ⬝ᵥ y = 0 := by
  rw [eq_comb_of_mem_C hx, eq_comb_of_mem_C hy]
  simp [sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, B_dot_B]

@[expose] def Umask (k : ℕ) : ℕ :=
  [0xe, 0x1f, 0x10f, 0x100f, 0x1000f, 0x11111, 0xa, 0xc, 0x5f, 0x3f, 0x50f, 0x30f].getD k 0

private theorem B_dot_U : ∀ i k : Fin 12, B i ⬝ᵥ bvec 24 (Umask k) = if i = k then 1 else 0 := by
  intro i k
  rw [B_eq_bvec, bvec_dotProduct]
  revert i k; decide

private noncomputable def dotB : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 12 → ZMod 2) :=
  (Matrix.of B).mulVecLin

private theorem dotB_apply (x : Fin 24 → ZMod 2) (i : Fin 12) : dotB x i = B i ⬝ᵥ x := rfl

private theorem dotB_surjective : Function.Surjective dotB := by
  intro c
  refine ⟨∑ k, c k • bvec 24 (Umask k), funext fun i => ?_⟩
  simp [dotB_apply, dotProduct_sum, dotProduct_smul, B_dot_U]

private theorem C_eq_ker_dotB : C = LinearMap.ker dotB := by
  have hle : C ≤ LinearMap.ker dotB := fun y hy =>
    funext fun i => by rw [dotB_apply]; exact dotProduct_eq_zero (B_mem_C i) hy
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have h := LinearMap.finrank_range_add_finrank_ker dotB
  rw [LinearMap.range_eq_top.2 dotB_surjective, finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at h
  rw [finrank_C]
  omega

theorem mem_C_iff_forall_dotProduct (x : Fin 24 → ZMod 2) :
    x ∈ C ↔ ∀ y ∈ C, x ⬝ᵥ y = 0 := by
  refine ⟨fun hx y hy => dotProduct_eq_zero hx hy, fun h => ?_⟩
  rw [C_eq_ker_dotB]
  exact funext fun i => by rw [dotB_apply, dotProduct_comm]; exact h _ (B_mem_C i)


end CFSG.Monster.Code
