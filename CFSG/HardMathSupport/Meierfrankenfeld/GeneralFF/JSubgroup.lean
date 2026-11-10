module

public import CFSG.RankThree.FFModules.ElemBestOffender

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

open CFSG.RankThree.FFModules
open scoped commutatorElement

section Defs

variable {X : Type*} [Group X] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def bestOffenderSub (ρ : Representation (ZMod 2) X W) : Subgroup X :=
  ⨆ (A : Subgroup X) (_ : IsElemBestOffender ρ A), A


theorem le_bestOffenderSub {ρ : Representation (ZMod 2) X W} {A : Subgroup X}
    (hA : CFSG.IsElementaryAbelian 2 A) (hb : IsBestOffender ρ A) :
    A ≤ bestOffenderSub ρ :=
  le_iSup₂_of_le A ⟨hA, hb⟩ le_rfl

theorem bestOffenderSub_le {ρ : Representation (ZMod 2) X W} {C : Subgroup X}
    (h : ∀ A : Subgroup X, CFSG.IsElementaryAbelian 2 A → IsBestOffender ρ A → A ≤ C) :
    bestOffenderSub ρ ≤ C :=
  iSup₂_le fun A hA => h A hA.1 hA.2

theorem bestOffenderSub_normal (ρ : Representation (ZMod 2) X W) :
    (bestOffenderSub ρ).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hle : bestOffenderSub ρ ≤ (bestOffenderSub ρ).comap (MulAut.conj g).toMonoidHom := by
    refine bestOffenderSub_le fun A hA hb => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    obtain ⟨hA', hb'⟩ := IsElemBestOffender.conj ⟨hA, hb⟩ g
    exact le_bestOffenderSub hA' hb'
  exact hle hn

theorem bestOffenderSub_eq_iSup_ne_bot (ρ : Representation (ZMod 2) X W) :
    bestOffenderSub ρ = ⨆ (A : Subgroup X) (_ : A ≠ ⊥ ∧ IsElemBestOffender ρ A), A := by
  refine le_antisymm (bestOffenderSub_le fun A hA hb => ?_)
    (iSup₂_le fun A hA => le_bestOffenderSub hA.2.1 hA.2.2)
  by_cases h : A = ⊥
  · exact (le_of_eq h).trans bot_le
  · exact le_iSup₂_of_le A ⟨h, hA, hb⟩ le_rfl


theorem commutator_conj_mem {J K : Subgroup X} {x y : X} (hx : x ∈ J)
    (hy : y ∈ ⁅K, J⁆) : x * y * x⁻¹ ∈ ⁅K, J⁆ := by
  have h : ⁅K, J⁆ ≤ (⁅K, J⁆).comap (MulAut.conj x).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro k hk j hj
    have key : x * ⁅k, j⁆ * x⁻¹ = ⁅k, x⁆⁻¹ * ⁅k, x * j⁆ := by
      simp only [commutatorElement_def]
      group
    change (MulAut.conj x) ⁅k, j⁆ ∈ ⁅K, J⁆
    rw [MulAut.conj_apply, key]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hk hx))
      (Subgroup.commutator_mem_commutator hk (Subgroup.mul_mem _ hx hj))
  have := h hy
  simpa [MulAut.conj_apply] using this

end Defs

section TwoElements

variable {X : Type*} [Group X]


theorem commutator_eq_one_iff {a b : X} : ⁅a, b⁆ = 1 ↔ a * b = b * a := by
  constructor
  · intro h
    have h' : a * b * a⁻¹ * b⁻¹ = 1 := by simpa [commutatorElement_def] using h
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h', one_mul]
  · intro h
    simp only [commutatorElement_def]
    calc a * b * a⁻¹ * b⁻¹ = (b * a) * a⁻¹ * b⁻¹ := by rw [h]
      _ = 1 := by group

theorem commutator_eq_bot_iff {K J : Subgroup X} :
    ⁅K, J⁆ = ⊥ ↔ ∀ k ∈ K, ∀ j ∈ J, ⁅k, j⁆ = 1 := by
  rw [← le_bot_iff, Subgroup.commutator_le]
  simp


end TwoElements

end CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
