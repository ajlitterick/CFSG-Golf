module

public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LieType.Chevalley.PositiveRootCollection

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial

variable {τ : Tag}


theorem height_pos_of_forall_height_le
    {θ : Fin τ.rank → ℤ}
    (hmax : ∀ γ, IsRoot τ γ → height γ ≤ height θ) : 0 < height θ := by
  have h := hmax _ (isRoot_single τ ⟨0, τ.rank_pos⟩)
  rw [height_single] at h
  omega

theorem not_isRoot_nsmul_add_nsmul_of_forall_height_le
    {θ β : Fin τ.rank → ℤ}
    (hmax : ∀ γ, IsRoot τ γ → height γ ≤ height θ) (hβp : 0 < height β) {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) : ¬IsRoot τ (a • θ + b • β) := by
  intro h
  have h1 := hmax _ h
  have hθp := height_pos_of_forall_height_le hmax
  rw [height_nsmul_add_nsmul] at h1
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith

theorem commute_pinnedX_of_forall_height_le
    (R : Type) [CommRing R] {θ β : Fin τ.rank → ℤ}
    (hθ : IsRoot τ θ) (hmax : ∀ γ, IsRoot τ γ → height γ ≤ height θ) (hβ : IsRoot τ β)
    (hβp : 0 < height β) (c d : R) :
    Commute (pinnedX τ R θ c) (pinnedX τ R β d) := by
  by_cases hθβ : θ = β
  · subst hθβ
    rw [Commute, SemiconjBy, ← pinnedX_add, ← pinnedX_add, add_comm]
  · have hc := commutator_rootSubgroup_le R hθ hβ (height_pos_of_forall_height_le hmax) hβp hθβ
    have hbot : (⨆ (γ : Fin τ.rank → ℤ) (_ : IsRoot τ γ ∧
        ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ = a • θ + b • β), rootSubgroup τ R γ) = ⊥ := by
      refine iSup₂_eq_bot.2 ?_
      rintro γ ⟨hγ, a, b, ha, hb, rfl⟩
      exact absurd hγ (not_isRoot_nsmul_add_nsmul_of_forall_height_le hmax hβp ha hb)
    rw [hbot] at hc
    have hmem := hc (Subgroup.commutator_mem_commutator (mem_rootSubgroup.2 ⟨c, rfl⟩)
      (mem_rootSubgroup.2 ⟨d, rfl⟩))
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem

section CharTwo

variable {K : Type} [Field K]

theorem pinnedX_one_mul_self
    (h2 : (2 : K) = 0) (α : Fin τ.rank → ℤ) :
    pinnedX τ K α 1 * pinnedX τ K α 1 = 1 := by
  rw [← pinnedX_add, one_add_one_eq_two, h2, pinnedX_zero]

theorem pinnedX_one_ne_one
    (α : Fin τ.rank → ℤ) : pinnedX τ K α 1 ≠ 1 := fun h =>
  one_ne_zero (pinnedX_injective τ K α (h.trans (pinnedX_zero τ K α).symm))

theorem pinnedX_one_ne_pinnedX_one
    {θ β : Fin τ.rank → ℤ} (hθ : IsRoot τ θ ∧ 0 < height θ)
    (hβ : IsRoot τ β ∧ 0 < height β) (hne : θ ≠ β) :
    pinnedX τ K θ 1 ≠ pinnedX τ K β 1 := fun h => by
  have hinj : Function.Injective ![θ, β] := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij hne
    · exact absurd hij.symm hne
    · rfl
  have hpos : ∀ i, IsRoot τ (![θ, β] i) ∧ 0 < height (![θ, β] i) := by
    intro i
    fin_cases i
    · exact hθ
    · exact hβ
  have key := (positive_root_product_injectivity τ K ![θ, β] hinj hpos).2
    (a₁ := ![1, 0]) (a₂ := ![0, 1]) (by
      simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ, pinnedX_zero, one_mul]
      exact h)
  have := congrFun key 0
  simp at this

theorem entrywise_pinnedX_one
    (δ : K →+* K) (α : Fin τ.rank → ℤ) :
    entrywise δ (pinnedX τ K α 1 : Module.End K (RootModule τ K)) = pinnedX τ K α 1 := by
  rw [entrywise_pinnedX, map_one]


end CharTwo


end CFSG.LieType.Chevalley
