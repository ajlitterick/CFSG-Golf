module

public import CFSG.Milestones.ASVolI.F4Native
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

section Generic


theorem burnsideF45_center_quotient_eq_bot {G : Type*} [Group G]
    (h : Subgroup.center G = ⊥) : Subgroup.center (G ⧸ Subgroup.center G) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  induction z using QuotientGroup.induction_on with
  | H g =>
    have hg : g ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun k => by
      have hk := Subgroup.mem_center_iff.1 hz (k : G ⧸ Subgroup.center G)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, h,
        Subgroup.mem_bot] at hk
      exact inv_mul_eq_one.1 hk
    rw [h, Subgroup.mem_bot] at hg
    rw [hg, QuotientGroup.mk_one]
    exact Subgroup.one_mem _


end Generic

section G2dRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley


end G2dRoot

section G2d

open CFSG.Blueprint CFSG.Blueprint.Chevalley


end G2d

section TitsRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots


end TitsRoot

section Tits

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots


end Tits

section Clause2


end Clause2

end CFSG.ASVolI
