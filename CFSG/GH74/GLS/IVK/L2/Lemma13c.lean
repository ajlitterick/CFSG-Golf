module

public import CFSG.GH74.GLS.IVK.L2.Fixed14a
public import CFSG.Dihedral.GorensteinWalter.PSL2OddCentralizerNormalizer

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter
open scoped Pointwise

section Quadratic

theorem isSquare_mul_of_not_isSquare {F : Type*} [Field F] [Fintype F] {a b : F}
    (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) : IsSquare (a * b) := by
  classical
  have ha0 : a ≠ 0 := fun h => ha (h ▸ IsSquare.zero)
  have hb0 : b ≠ 0 := fun h => hb (h ▸ IsSquare.zero)
  have h1 := quadraticChar_neg_one_iff_not_isSquare.mpr ha
  have h2 := quadraticChar_neg_one_iff_not_isSquare.mpr hb
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0), map_mul, h1, h2]
  norm_num


end Quadratic

section Embedding


end Embedding


section Normalizer

variable {M : Type*} [Group M]

theorem mem_normalizer_subgroupOf_iff (D X : Subgroup M) (hXD : X ≤ D) (g : D) :
    (g : M) ∈ normalizer (X : Set M) ↔ g ∈ normalizer ((X.subgroupOf D : Subgroup D) : Set D) := by
  have h := Subgroup.comap_normalizer_eq_of_le_range (H := X) (f := D.subtype) (by
    intro x hx
    exact ⟨⟨x, hXD hx⟩, rfl⟩)
  have h2 : g ∈ (normalizer (X : Set M)).comap D.subtype ↔ (g : M) ∈ normalizer (X : Set M) :=
    Iff.rfl
  rw [← h2, h]
  rfl

theorem mem_normalizer_map_iff {G H : Type*} [Group G] [Group H] (Ψ : G →* H)
    (hΨ : Function.Injective Ψ) (Y : Subgroup G) (g : G) :
    g ∈ normalizer (Y : Set G) ↔ Ψ g ∈ normalizer ((Y.map Ψ : Subgroup H) : Set H) := by
  have h := Subgroup.comap_normalizer_eq_of_le_range (H := Y.map Ψ) (f := Ψ) (by
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩)
  rw [Subgroup.comap_map_eq_self_of_injective hΨ] at h
  have h2 : g ∈ (normalizer ((Y.map Ψ : Subgroup H) : Set H)).comap Ψ ↔
      Ψ g ∈ normalizer ((Y.map Ψ : Subgroup H) : Set H) := Iff.rfl
  rw [← h2, h]


end Normalizer

section Main

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem mem_stabilizer_subgroup_iff (α : MulAut K) (W : Subgroup K) :
    α ∈ MulAction.stabilizer (MulAut K) W ↔ ∀ k, α k ∈ W ↔ k ∈ W := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h k
    have := SetLike.ext_iff.1 h (α k)
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at this
    simpa using this.symm
  · intro h
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have := h (α⁻¹ • x)
    simpa using this.symm

omit [Finite K] in
theorem mem_normalizer_map_conj_iff (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (g : MulAut K) (X : Subgroup K) :
    g ∈ normalizer ((X.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
      Set (MulAut K)) ↔ g ∈ MulAction.stabilizer (MulAut K) X := by
  rw [Subgroup.mem_normalizer_iff, mem_stabilizer_subgroup_iff]
  have key : ∀ (h : MulAut K) (k : K), h * MulAut.conj k * h⁻¹ = MulAut.conj (h k) :=
    fun h k => mul_conj_mul_inv_eq_conj_apply h k
  have hmem : ∀ k : K, MulAut.conj k ∈ X.map (MulAut.conj : K →* MulAut K) ↔ k ∈ X :=
    fun k => Subgroup.mem_map_iff_mem hinj
  constructor
  · intro h k
    calc g k ∈ X ↔ MulAut.conj (g k) ∈ X.map (MulAut.conj : K →* MulAut K) := (hmem _).symm
      _ ↔ g * MulAut.conj k * g⁻¹ ∈ X.map (MulAut.conj : K →* MulAut K) := by rw [key]
      _ ↔ MulAut.conj k ∈ X.map (MulAut.conj : K →* MulAut K) := (h _).symm
      _ ↔ k ∈ X := hmem _
  · intro h y
    constructor
    · rintro ⟨k, hk, rfl⟩
      show g * MulAut.conj k * g⁻¹ ∈ _
      rw [key]
      exact (hmem _).mpr ((h k).mpr hk)
    · intro hy
      obtain ⟨k', hk', hk'eq⟩ := hy
      have hy' : y = MulAut.conj (g⁻¹ k') := by
        rw [← key g⁻¹ k']
        have : (MulAut.conj k') = g * y * g⁻¹ := hk'eq
        rw [this]
        group
      rw [hy']
      refine (hmem _).mpr ?_
      have := (h (g⁻¹ k')).mp (by simpa using hk')
      exact this


end Main

end CFSG.GH74.GLS.IVK
