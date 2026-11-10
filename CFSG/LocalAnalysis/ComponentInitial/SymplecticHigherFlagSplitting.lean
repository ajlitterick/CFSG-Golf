module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagExtension
public import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Module Submodule SymplecticFlag
open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def IsSelfDualChain (B : BilinForm K V) (N : ℕ) (F : ℕ → Submodule K V) : Prop :=
  F 0 = ⊥ ∧ (∀ i < N, F i ≤ F (i + 1)) ∧ ∀ i ≤ N, B.orthogonal (F i) = F (N - i)

@[expose] def IsSelfDualFlag (B : BilinForm K V) (r : ℕ) (F : ℕ → Submodule K V) : Prop :=
  (∀ i ≤ 2 * r, finrank K (F i) = i) ∧ (∀ i < 2 * r, F i ≤ F (i + 1)) ∧
    ∀ i ≤ 2 * r, B.orthogonal (F i) = F (2 * r - i)

variable {B : BilinForm K V}

theorem IsSelfDualFlag.isSelfDualChain [FiniteDimensional K V] {r : ℕ}
    {F : ℕ → Submodule K V} (hF : IsSelfDualFlag B r F) : IsSelfDualChain B (2 * r) F :=
  ⟨Submodule.finrank_eq_zero.mp (hF.1 0 (Nat.zero_le _)), hF.2.1, hF.2.2⟩

theorem IsSelfDualChain.le {N : ℕ} {F : ℕ → Submodule K V} (hF : IsSelfDualChain B N F)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) : F i ≤ F j :=
  flag_le hF.2.1 hij hj

theorem IsSelfDualChain.top {N : ℕ} {F : ℕ → Submodule K V} (hF : IsSelfDualChain B N F) :
    F N = ⊤ := by
  have h := hF.2.2 0 (Nat.zero_le _)
  rw [hF.1, BilinForm.orthogonal_bot, Nat.sub_zero] at h
  exact h.symm

@[expose] def IsPairCompatible (B : BilinForm K V) (N : ℕ) (F : ℕ → Submodule K V) (e f : V) :
    Prop :=
  ∀ i ≤ N, ∀ u ∈ F i, (B f u = 0 ∨ e ∈ F i) ∧ (B e u = 0 ∨ f ∈ F i)

variable {N : ℕ} {F : ℕ → Submodule K V} {e f : V}

theorem IsPairCompatible.smul_left_mem (h : IsPairCompatible B N F e f) {i : ℕ} (hi : i ≤ N)
    {u : V} (hu : u ∈ F i) : B f u • e ∈ F i := by
  rcases (h i hi u hu).1 with h1 | h1
  · rw [h1, zero_smul]
    exact zero_mem _
  · exact smul_mem _ _ h1

theorem IsPairCompatible.smul_right_mem (h : IsPairCompatible B N F e f) {i : ℕ} (hi : i ≤ N)
    {u : V} (hu : u ∈ F i) : B e u • f ∈ F i := by
  rcases (h i hi u hu).2 with h1 | h1
  · rw [h1, zero_smul]
    exact zero_mem _
  · exact smul_mem _ _ h1

theorem IsPairCompatible.proj_mem (h : IsPairCompatible B N F e f) {i : ℕ} (hi : i ≤ N)
    {u : V} (hu : u ∈ F i) : u - B f u • e + B e u • f ∈ F i :=
  add_mem (sub_mem hu (h.smul_left_mem hi hu)) (h.smul_right_mem hi hu)

theorem isPairCompatible_of_first (hF : IsSelfDualChain B N F) {i₀ : ℕ} (hi₀ : i₀ ≤ N)
    (hbot : ∀ m < i₀, F m = ⊥) (he : e ∈ F i₀) (f : V) : IsPairCompatible B N F e f := by
  intro i hi u hu
  constructor
  · by_cases h : i₀ ≤ i
    · exact Or.inr (hF.le h hi he)
    · left
      rw [hbot i (by omega), mem_bot] at hu
      rw [hu, map_zero]
  · by_cases h : i ≤ N - i₀
    · left
      have hu' : u ∈ F (N - i₀) := hF.le h (Nat.sub_le _ _) hu
      rw [← hF.2.2 i₀ hi₀] at hu'
      exact hu' e he
    · right
      have h1 := hF.2.2 (N - i) (Nat.sub_le _ _)
      rw [hbot (N - i) (by omega), BilinForm.orthogonal_bot, Nat.sub_sub_self hi] at h1
      rw [← h1]
      trivial

theorem isPairCompatible_of_least {G : ℕ → Submodule K V} (hG : IsSelfDualChain B N G) {j : ℕ}
    (hj1 : 1 ≤ j) (hjN : j ≤ N) (he : e ∈ G j) (hf : f ∈ G (N + 1 - j)) :
    IsPairCompatible B N G e f := by
  intro i hi u hu
  constructor
  · by_cases h : j ≤ i
    · exact Or.inr (hG.le h hi he)
    · left
      have hu' : u ∈ G (j - 1) := hG.le (by omega) (by omega) hu
      have h1 := hG.2.2 (N + 1 - j) (by omega)
      rw [show N - (N + 1 - j) = j - 1 by omega] at h1
      rw [← h1] at hu'
      exact hu' f hf
  · by_cases h : N + 1 - j ≤ i
    · exact Or.inr (hG.le h hi hf)
    · left
      have hu' : u ∈ G (N - j) := hG.le (by omega) (by omega) hu
      rw [← hG.2.2 j hjN] at hu'
      exact hu' e he

theorem exists_partner {G : ℕ → Submodule K V} (hG : IsSelfDualChain B N G) {j : ℕ}
    (hj1 : 1 ≤ j) (hjN : j ≤ N) (he : e ∉ G (j - 1)) : ∃ f ∈ G (N + 1 - j), B f e = 1 := by
  have h1 := hG.2.2 (N + 1 - j) (by omega)
  rw [show N - (N + 1 - j) = j - 1 by omega] at h1
  rw [← h1, BilinForm.mem_orthogonal_iff] at he
  push Not at he
  obtain ⟨n, hn, hne⟩ := he
  exact ⟨(B n e)⁻¹ • n, smul_mem _ _ hn, by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hne]⟩

section Pair

variable (hB : B.IsAlt) (hfe : B f e = 1)
include hB hfe

theorem proj_mem_orthogonal (u : V) :
    u - B f u • e + B e u • f ∈ B.orthogonal (span K {e, f}) :=
  hB.sub_smul_add_smul_mem_orthogonal_span_pair hfe u

omit hB hfe in
theorem eq_proj_add (u : V) : u = (B f u • e - B e u • f) + (u - B f u • e + B e u • f) := by
  abel


theorem IsPairCompatible.sup_eq (h : IsPairCompatible B N F e f) {i : ℕ} (hi : i ≤ N) :
    F i ⊓ span K {e, f} ⊔ F i ⊓ B.orthogonal (span K {e, f}) = F i := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) fun u hu => ?_
  rw [eq_proj_add (B := B) (e := e) (f := f) u]
  refine add_mem_sup ⟨?_, ?_⟩ ⟨h.proj_mem hi hu, proj_mem_orthogonal hB hfe u⟩
  · exact sub_mem (h.smul_left_mem hi hu) (h.smul_right_mem hi hu)
  · exact sub_mem (smul_mem _ _ (subset_span (Set.mem_insert e {f})))
      (smul_mem _ _ (subset_span (Set.mem_insert_of_mem e (Set.mem_singleton f))))


theorem isSelfDualChain_comap (hF : IsSelfDualChain B N F) (h : IsPairCompatible B N F e f) :
    IsSelfDualChain (B.restrict (B.orthogonal (span K {e, f}))) N
      fun i => (F i).comap (B.orthogonal (span K {e, f})).subtype := by
  set Z := B.orthogonal (span K {e, f})
  refine ⟨by show (F 0).comap Z.subtype = ⊥; rw [hF.1, comap_bot, ker_subtype],
    fun i hi => comap_mono (hF.2.1 i hi), fun i hi => ?_⟩
  ext z
  simp only [BilinForm.mem_orthogonal_iff, mem_comap, subtype_apply, BilinForm.restrict_apply,
    LinearMap.domRestrict_apply]
  rw [← hF.2.2 i hi, BilinForm.mem_orthogonal_iff]
  have hz := (BilinForm.mem_orthogonal_span_pair_iff B).mp z.2
  constructor
  · intro hzF n hn
    have hP : n - B f n • e + B e n • f ∈ Z := proj_mem_orthogonal hB hfe n
    have h1 := hzF ⟨_, hP⟩ (h.proj_mem hi hn)
    simp only at h1
    have : B n z = B (n - B f n • e + B e n • f) z + B f n * B e z - B e n * B f z := by
      simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [this, h1, hz.1, hz.2]
    ring
  · intro hzF y hy
    exact hzF y hy

end Pair


end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
