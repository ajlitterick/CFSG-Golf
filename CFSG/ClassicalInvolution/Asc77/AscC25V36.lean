module

public import CFSG.ClassicalInvolution.Asc77.AscC25V30
public import CFSG.ClassicalInvolution.Asc77.AscC25V35

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Abstract

variable {G : Type} [Group G]

@[expose] def swapDiff {N : Subgroup G} {t : G} (ht2 : t * t = 1)
    (hconj : ∀ n ∈ N, t * n * t ∈ N) {Γ : Type*} [CommGroup Γ] (φ : N →* Γ) : N →* Γ :=
  MonoidHom.mk' (fun n => φ n * (φ ⟨t * n * t, hconj n n.2⟩)⁻¹) (by
    intro n m
    have e2 : (⟨t * ((n * m : N) : G) * t, hconj _ (n * m).2⟩ : N) =
        ⟨t * n * t, hconj n n.2⟩ * ⟨t * m * t, hconj m m.2⟩ := by
      apply Subtype.ext
      show t * ((n : G) * m) * t = (t * n * t) * (t * m * t)
      calc t * ((n : G) * m) * t = t * n * (t * t) * m * t := by rw [ht2]; group
        _ = (t * n * t) * (t * m * t) := by group
    rw [map_mul, e2, map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)

variable {N : Subgroup G} {t : G} (ht2 : t * t = 1) (hconj : ∀ n ∈ N, t * n * t ∈ N)
  {Γ : Type*} [CommGroup Γ] (φ : N →* Γ)

include ht2 in
theorem swapDiff_apply (n : G) (hn : n ∈ N) :
    swapDiff ht2 hconj φ ⟨n, hn⟩ = φ ⟨n, hn⟩ * (φ ⟨t * n * t, hconj n hn⟩)⁻¹ := rfl


theorem exists_swapDiff_eq_of_hT {C : Subgroup G} (hNC : N ≤ C)
    (hcov : ∀ c ∈ C, c ∈ N ∨ c * t ∈ N) {Γ : Type} [CommGroup Γ] (χ : N →* Γ) (δ : N →* ℤˣ)
    {a : G} (haN : a ∈ N)
    (hT : ∀ (B : Type) [CommGroup B] (π : ↥C →* B), π ⟨a, hNC haN⟩ = 1) :
    ∃ n : N, swapDiff ht2 hconj δ n = δ ⟨a, haN⟩ ∧ swapDiff ht2 hconj χ n = χ ⟨a, haN⟩ := by
  classical
  let ε : N →* ℤˣ × Γ := (swapDiff ht2 hconj δ).prod (swapDiff ht2 hconj χ)
  let E : Subgroup (ℤˣ × Γ) := ε.range
  have : E.Normal := Subgroup.normal_of_isMulCommutative E
  let ϕ₀ : N →* ((ℤˣ × Γ) ⧸ E) := (QuotientGroup.mk' E).comp (δ.prod χ)
  have hinv : ∀ (n : G) (hn : n ∈ N), ϕ₀ ⟨t * n * t, hconj n hn⟩ = ϕ₀ ⟨n, hn⟩ := by
    intro n hn
    change (QuotientGroup.mk (δ ⟨t * n * t, hconj n hn⟩, χ ⟨t * n * t, hconj n hn⟩) :
      (ℤˣ × Γ) ⧸ E) = QuotientGroup.mk (δ ⟨n, hn⟩, χ ⟨n, hn⟩)
    rw [QuotientGroup.eq]
    refine ⟨⟨n, hn⟩, ?_⟩
    change (swapDiff ht2 hconj δ ⟨n, hn⟩, swapDiff ht2 hconj χ ⟨n, hn⟩) = _
    rw [swapDiff_apply ht2 hconj δ n hn, swapDiff_apply ht2 hconj χ n hn]
    ext
    · simp [mul_comm]
    · simp [mul_comm]
  obtain ⟨ϕ, hϕ⟩ := exists_hom_extension_of_index_two C N hNC t ht2 hcov hconj ϕ₀ hinv
  have h1 := hT ((ℤˣ × Γ) ⧸ E) ϕ
  rw [hϕ a haN] at h1
  change (QuotientGroup.mk (δ ⟨a, haN⟩, χ ⟨a, haN⟩) : (ℤˣ × Γ) ⧸ E) = 1 at h1
  rw [QuotientGroup.eq_one_iff] at h1
  obtain ⟨n, hn⟩ := h1
  exact ⟨n, congrArg Prod.fst hn, congrArg Prod.snd hn⟩


end Abstract

section Main


end Main

section Proof


end Proof

end CFSG.ClassicalInvolution.Asc77.C25V
