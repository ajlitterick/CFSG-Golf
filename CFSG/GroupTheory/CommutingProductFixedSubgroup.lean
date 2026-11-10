module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_of_commute {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G} (hg : g ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  let S : Subgroup G :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, a * b = g}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        rw [mul_assoc a b (a' * b'), ← mul_assoc b a' b', ← hcomm a' ha' b hb]
        simp only [mul_assoc]
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [mul_inv_rev, hcomm a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)] }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩)
  exact hle hg

theorem commutatorElement_mul_of_commute {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {a₁ a₂ b₁ b₂ : G} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) : ⁅a₁ * b₁, a₂ * b₂⁆ = ⁅a₁, a₂⁆ * ⁅b₁, b₂⁆ := by
  let φ : A × B →* G := MonoidHom.noncommCoprod A.subtype B.subtype fun a b => hcomm a a.2 b b.2
  have h := map_commutatorElement φ (⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩) (⟨a₂, ha₂⟩, ⟨b₂, hb₂⟩)
  exact h.symm


end CFSG.GroupTheory
