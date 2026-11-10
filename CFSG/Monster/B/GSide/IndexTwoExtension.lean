module

public import CFSG.Monster.B.Recog.GenericIndexTwo
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B.Recog CFSG.Monster.B.Recog.IndexTwo

variable {A E G : Type*} [Group A] [Group E] [Group G]


theorem exists_hom_of_index_two_of_norm (ι : A →* E) (hι : Function.Injective ι)
    (h2 : ι.range.index = 2) {s : E} (hs : s ∉ ι.range) (σ : A ≃* A)
    (hσ : ∀ a, s * ι a * s⁻¹ = ι (σ a)) (θ : A →* G) (t : G)
    (ht : ∀ a, t * θ a * t⁻¹ = θ (σ a)) {τ ρ d : A} (hτ : s * s = ι τ) (hρ : t * t = θ ρ)
    (hd : d ∈ Subgroup.center A) (hτρ : τ = ρ * (d * σ d)) :
    ∃ f : E →* G, (∀ a, f (ι a) = θ a) ∧ f s = t * θ d := by
  have hσd : σ d ∈ Subgroup.center A := Subgroup.mem_center_iff.2 fun a => by
    have := Subgroup.mem_center_iff.1 hd (σ.symm a)
    simpa using congrArg σ this
  have hdc : ∀ a, θ d * θ a * (θ d)⁻¹ = θ a := fun a => by
    rw [← map_mul, ← Subgroup.mem_center_iff.1 hd a, map_mul, mul_inv_cancel_right]
  have hu : ∀ a, t * θ d * θ a * (t * θ d)⁻¹ = θ (σ a) := fun a => by
    calc t * θ d * θ a * (t * θ d)⁻¹ = t * (θ d * θ a * (θ d)⁻¹) * t⁻¹ := by group
      _ = θ (σ a) := by rw [hdc, ht]
  have hu2 : t * θ d * (t * θ d) = θ τ := by
    have h1 : t * θ d = θ (σ d) * t := by rw [← ht, inv_mul_cancel_right]
    have hc1 : σ d * ρ = ρ * σ d := (Subgroup.mem_center_iff.1 hσd ρ).symm
    have hc2 : σ d * d = d * σ d := (Subgroup.mem_center_iff.1 hσd d).symm
    calc t * θ d * (t * θ d) = t * θ d * t * θ d := by group
      _ = θ (σ d) * (t * t) * θ d := by rw [h1]; group
      _ = θ (σ d * ρ * d) := by rw [hρ, map_mul, map_mul]
      _ = θ τ := by rw [hτρ, hc1, mul_assoc, hc2]
  exact exists_hom ι θ hι h2 hs (t * θ d) σ τ hσ hu hτ hu2

theorem exists_hom_of_index_two (ι : A →* E) (hι : Function.Injective ι)
    (h2 : ι.range.index = 2) {s : E} (hs : s ∉ ι.range) (σ : A ≃* A)
    (hσ : ∀ a, s * ι a * s⁻¹ = ι (σ a)) (θ : A →* G) (hθ : Function.Injective θ) (t : G)
    (b : A) (ht : ∀ a, t * θ a * t⁻¹ = θ (σ (b * a * b⁻¹))) (ht2 : t * t ∈ θ.range)
    (hnorm : ∀ c ∈ Subgroup.center A, σ c = c → ∃ d ∈ Subgroup.center A, c = d * σ d) :
    ∃ f : E →* G, (∀ a, f (ι a) = θ a) ∧ ∃ d ∈ Subgroup.center A, f s = t * θ (b⁻¹ * d) := by
  set t₁ := t * θ b⁻¹ with ht₁
  have ht₁σ : ∀ a, t₁ * θ a * t₁⁻¹ = θ (σ a) := fun a => by
    have := ht (b⁻¹ * a * b)
    rw [show b * (b⁻¹ * a * b) * b⁻¹ = a by group] at this
    rw [← this, ht₁, map_mul, map_mul, map_inv]
    group
  obtain ⟨ρ, hρ⟩ := ht2
  set ρ₁ := σ b⁻¹ * ρ * b⁻¹ with hρ₁
  have ht₁sq : t₁ * t₁ = θ ρ₁ := by
    have h1 : t * θ b⁻¹ * t⁻¹ = θ (σ b⁻¹) := by
      have := ht b⁻¹
      rwa [show b * b⁻¹ * b⁻¹ = b⁻¹ by group] at this
    calc t₁ * t₁ = t * θ b⁻¹ * t⁻¹ * (t * t) * θ b⁻¹ := by rw [ht₁]; group
      _ = θ ρ₁ := by rw [h1, ← hρ, hρ₁, map_mul, map_mul]
  obtain ⟨τ, hτ, hτσ, hτc⟩ := exists_sq ι hι h2 σ.toMonoidHom s hσ
  simp only [MulEquiv.coe_toMonoidHom] at hτσ hτc
  have hρ₁c : ∀ a, ρ₁ * a * ρ₁⁻¹ = τ * a * τ⁻¹ := fun a => hθ (by
    rw [map_mul, map_mul, map_inv, ← ht₁sq, ← hτc, ← ht₁σ, ← ht₁σ]
    group)
  have hcen : ρ₁⁻¹ * τ ∈ Subgroup.center A := Subgroup.mem_center_iff.2 fun a => by
    have := hρ₁c a
    calc a * (ρ₁⁻¹ * τ) = ρ₁⁻¹ * (ρ₁ * a * ρ₁⁻¹) * τ := by group
      _ = ρ₁⁻¹ * τ * a := by rw [this]; group
  have hρ₁σ : σ ρ₁ = ρ₁ := hθ (by
    rw [← ht₁σ, ← ht₁sq]
    group)
  have hfix : σ (ρ₁⁻¹ * τ) = ρ₁⁻¹ * τ := by rw [map_mul, map_inv, hρ₁σ, hτσ]
  obtain ⟨d, hd, hcd⟩ := hnorm _ hcen hfix
  have hτρ : τ = ρ₁ * (d * σ d) := by rw [← hcd, mul_inv_cancel_left]
  obtain ⟨f, hf, hfs⟩ :=
    exists_hom_of_index_two_of_norm ι hι h2 hs σ hσ θ t₁ ht₁σ hτ ht₁sq hd hτρ
  refine ⟨f, hf, d, hd, ?_⟩
  rw [hfs, ht₁, mul_assoc, ← map_mul]


end CFSG.Monster.B.GSide
