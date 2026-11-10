module

public import CFSG.Assembly.Defs
public import CFSG.Open.FusionDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.LocalAnalysis.ABGTheoremB.Basic

public section

namespace CFSG.Foundations.SteinbergCA

open scoped commutatorElement


theorem quasisimple_iff (Q : Type*) [Group Q] :
    (CFSG.IsQuasisimple Q ↔ Group.IsPerfect Q ∧ IsSimpleGroup (Q ⧸ Subgroup.center Q) ∧
      ∃ a b : Q ⧸ Subgroup.center Q, a * b ≠ b * a) ∧
    (CFSG.IsQuasisimple Q ↔ CFSG.Assembly.IsQuasisimple Q) ∧
    (CFSG.IsQuasisimple Q ↔ CFSG.Open.IsQuasisimple Q) ∧
    (CFSG.IsQuasisimple Q ↔ CFSG.GorensteinWalter.IsQuasisimple Q) := by
  have hasm : CFSG.IsQuasisimple Q ↔ CFSG.Assembly.IsQuasisimple Q := by
    constructor
    · rintro ⟨hperf, hsimple, -⟩
      exact ⟨Group.isPerfect_def.mp hperf, hsimple⟩
    · rintro ⟨hcomm, hsimple⟩
      refine ⟨Group.isPerfect_def.mpr hcomm, hsimple, ?_⟩
      by_contra hab
      push Not at hab
      have hle : commutator Q ≤ Subgroup.center Q := by
        rw [commutator_def, Subgroup.commutator_le]
        intro x _ y _
        rw [← QuotientGroup.eq_one_iff]
        change (QuotientGroup.mk' (Subgroup.center Q)) ⁅x, y⁆ = 1
        rw [map_commutatorElement, commutatorElement_def,
          hab ((QuotientGroup.mk' (Subgroup.center Q)) x), mul_inv_cancel_right,
          mul_inv_cancel]
      rw [hcomm] at hle
      obtain ⟨a, b, hne⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      exact hne (QuotientGroup.eq.mpr (hle (Subgroup.mem_top _)))
  refine ⟨Iff.rfl, hasm, hasm, hasm.trans ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩⟩
  obtain ⟨-, hsimple⟩ := h
  obtain ⟨a, b, hne⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨x, y, fun hxy => hne (by rw [hxy])⟩


end CFSG.Foundations.SteinbergCA
