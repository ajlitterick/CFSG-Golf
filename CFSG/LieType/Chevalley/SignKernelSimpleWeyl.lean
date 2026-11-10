module

public import CFSG.LieType.Chevalley.KernelComponentLength

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

variable {τ : Tag} {M : Type*} [CommGroup M]

@[expose] def componentRoots (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (i : KernelComponent χ) : Set (Fin τ.rank → ℤ) :=
  {α | ∃ h : α ∈ kernelRoots χ, (⟦⟨α, h⟩⟧ : KernelComponent χ) = i}

variable {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem chi_neg {α : Fin τ.rank → ℤ} (h : χ (Multiplicative.ofAdd α) = 1) :
    χ (Multiplicative.ofAdd (-α)) = 1 := by
  rw [ofAdd_neg, map_inv, h, inv_one]

theorem chi_zsmul {α : Fin τ.rank → ℤ} (h : χ (Multiplicative.ofAdd α) = 1) (n : ℤ) :
    χ (Multiplicative.ofAdd (n • α)) = 1 := by
  rw [ofAdd_zsmul, map_zpow, h, _root_.one_zpow]

theorem isRootComponent_componentRoots
    (i : KernelComponent χ) :
    IsRootComponent (componentRoots χ i) := by
  have hmk : ∀ {α β : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots χ) (hβ : β ∈ kernelRoots χ),
      iform α β ≠ 0 → (⟦⟨α, hα⟩⟧ : KernelComponent χ) = ⟦⟨β, hβ⟩⟧ :=
    fun hα hβ h => mk_eq_of_iform_ne_zero (α := ⟨_, hα⟩) (β := ⟨_, hβ⟩) h
  refine ⟨fun α ⟨h, _⟩ => h.1, fun α ⟨h, hi⟩ => ?_, fun α ⟨hα, hαi⟩ β ⟨hβ, hβi⟩ hr => ?_,
    fun α ⟨hα, hαi⟩ β ⟨hβ, hβi⟩ => ?_, fun S hS horth => ?_⟩
  ·
    have hn : -α ∈ kernelRoots χ := ⟨IsRoot.neg h.1, chi_neg h.2⟩
    refine ⟨hn, (hmk hn h ?_).trans hi⟩
    rw [← neg_one_smul ℤ α, iform_smul_left]
    have := iform_self_pos_of_isRoot h.1
    omega
  ·
    have hs : α + β ∈ kernelRoots χ := ⟨hr, by
      rw [ofAdd_add, map_mul, hα.2, hβ.2, one_mul]⟩
    have hpos := iform_self_pos_of_isRoot hr
    rw [iform_add_right] at hpos
    by_cases h1 : iform (α + β) α = 0
    · rw [h1, zero_add] at hpos
      exact ⟨hs, (hmk hs hβ hpos.ne').trans hβi⟩
    · exact ⟨hs, (hmk hs hα h1).trans hαi⟩
  ·
    have hβr := hβ.1
    have hr : rootReflection β • α ∈ kernelRoots χ := ⟨IsRoot.smul hα.1 _, by
      rw [rootReflection_smul hβr, sub_eq_add_neg, ofAdd_add, map_mul, hα.2, one_mul,
        ← neg_smul, chi_zsmul hβ.2]⟩
    by_cases h0 : iform β α = 0
    · rw [rootReflection_smul_of_iform_eq_zero hβr h0]
      exact ⟨hα, hαi⟩
    · refine ⟨hr, (hmk hr hβ ?_).trans hβi⟩
      have h1 := iform_smul (rootReflection β) α β
      rw [rootReflection_smul_self hβr, ← neg_one_smul ℤ β, iform_smul_right] at h1
      intro h2
      rw [h2, mul_zero] at h1
      exact h0 (by rw [iform_comm]; exact h1.symm)
  ·
    by_cases hne : S = ∅
    · exact Or.inl hne
    right
    obtain ⟨α, hαS⟩ := Set.nonempty_iff_ne_empty.2 hne
    obtain ⟨hα, hαi⟩ := hS hαS
    refine Set.Subset.antisymm hS fun γ hγ => ?_
    obtain ⟨hγk, hγi⟩ := hγ
    have key : ∀ x y : kernelRoots χ, Relation.EqvGen (fun α β : kernelRoots χ =>
        (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) x y →
        (⟦x⟧ : KernelComponent χ) = i → ((x : Fin τ.rank → ℤ) ∈ S ↔ (y : Fin τ.rank → ℤ) ∈ S) := by
      intro x y hxy
      induction hxy with
      | rel x y hrel =>
        intro hxi
        have hyi : (⟦y⟧ : KernelComponent χ) = i :=
          (Quotient.sound (Relation.EqvGen.rel x y hrel)).symm.trans hxi
        rw [dotProduct_mulVec_eq_iform] at hrel
        constructor
        · intro hx
          by_contra hy
          exact hrel (horth _ hx _ ⟨y.2, hyi⟩ hy)
        · intro hy
          by_contra hx
          exact hrel (by rw [iform_comm]; exact horth _ hy _ ⟨x.2, hxi⟩ hx)
      | refl x => exact fun _ => Iff.rfl
      | symm x y hxy ih =>
        intro hyi
        exact (ih ((Quotient.sound hxy).trans hyi)).symm
      | trans x y z hxy hyz ih1 ih2 =>
        intro hxi
        exact (ih1 hxi).trans (ih2 ((Quotient.sound hxy).symm.trans hxi))
    have hrel := Quotient.exact (hαi.trans hγi.symm)
    exact (key ⟨α, hα⟩ ⟨γ, hγk⟩ hrel hαi).1 hαS


end CFSG.LieType.Chevalley
