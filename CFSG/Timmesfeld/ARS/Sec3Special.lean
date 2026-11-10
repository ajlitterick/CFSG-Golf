module

public import CFSG.Timmesfeld.ARS.Sec3Lines

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec3

theorem conjSub_ne_of_special (hR : IsRootClass R) (hiso : NoIsolated R) {A B : Subgroup G}
    (hA : A ∈ R) (hB : B ∈ R) (h : Special R A B) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    conjSub B a ≠ B := by
  intro hBa
  obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hB
  apply hb1
  refine eq_one_of_commute_of_special hR hiso hA hB h ha ha1 hb ?_
  have hne : B ≠ ⁅A, B⁆ := by
    have := h.symm.ne_commutator hR
    rwa [Subgroup.commutator_comm] at this
  have h1 : ⁅a, b⁆ ∈ B ⊓ ⁅A, B⁆ := by
    refine ⟨?_, Subgroup.commutator_mem_commutator ha hb⟩
    rw [commutatorElement_def]
    refine B.mul_mem ?_ (B.inv_mem hb)
    rw [← hBa]
    exact conj_mem_conjSub a hb
  rw [inf_eq_bot hR hiso hB h.1 hne, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem sup_conjSub_eq_of_special [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (h : Special R A B) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) : B ⊔ conjSub B a = ⁅B, A⁆ ⊔ B :=
  sup_eq_of_le_of_commuting hR hiso h.symm.1 hB hB (hR.conjSub_mem hB a) h.symm.2.1 le_sup_right
    (conjSub_le_commutator_sup ha) (conjSub_ne_of_special hR hiso hA hB h ha ha1).symm


end Sec3

open Sec3


end CFSG.Timmesfeld.ARS
