module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Basic
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.LocalAnalysis.PreuniquenessRankFour.CriticalSubgroup

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem le_oddCore {N : Subgroup X} (hN : N.Normal) (hodd : Odd (Nat.card N)) : N ≤ oddCore X :=
  le_sSup ⟨hN, hodd⟩

theorem pCore_eq_bot_of_oddCore {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hO : oddCore X = ⊥) :
    pCore q X = ⊥ := by
  have : (pCore q X).Normal := pCore_normal
  refine le_bot_iff.mp (hO ▸ le_oddCore this ?_)
  obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup q (pCore q X)).exists_card_eq
  rw [hk]
  exact Odd.pow ((Fact.out : q.Prime).odd_of_ne_two hq2)

theorem fittingSubgroup_le_pCore_two (hO : oddCore X = ⊥) : fittingSubgroup X ≤ pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine iSup_le fun q => ?_
  have hq : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.2
  have : Fact (q : ℕ).Prime := ⟨hq⟩
  by_cases hq2 : (q : ℕ) = 2
  · rw [hq2]
  · rw [pCore_eq_bot_of_oddCore hq2 hO]
    exact bot_le

variable [Group.IsPerfect X] {K : Subgroup X} [K.Normal] [IsSimpleGroup (X ⧸ K)]

theorem centralizer_pCore_two_le (hK : Group.IsSolvable K) (hO : oddCore X = ⊥)
    (hq : ¬ IsQuasisimple X) : Subgroup.centralizer (pCore 2 X : Set X) ≤ pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, hq', hC⟩ := exists_centralizer_pCore_le hK hq
  have : Fact q.Prime := ⟨hq'⟩
  have hq2 : q = 2 := by
    by_contra hq2
    rw [pCore_eq_bot_of_oddCore hq2 hO] at hC
    have htop : (⊤ : Subgroup X) ≤ K := by
      intro g _
      apply hC
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hx
      rw [hx, one_mul, mul_one]
    exact (QuotientGroup.nontrivial_iff.mp inferInstance) (top_le_iff.mp htop)
  subst hq2
  set C := Subgroup.centralizer (pCore 2 X : Set X) with hCdef
  have : (pCore 2 X).Normal := pCore_normal
  have hCsol : Group.IsSolvable C := by
    have := hK
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hC)
  have hFC : (fittingSubgroup C).map C.subtype ≤ pCore 2 X :=
    (le_sSup ⟨inferInstance, Group.nilpotent_of_surjective (C.subtype.subgroupMap
      (fittingSubgroup C)) (C.subtype.subgroupMap_surjective _)⟩ :
        _ ≤ fittingSubgroup X).trans (fittingSubgroup_le_pCore_two hO)
  have hCC := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hCsol
  intro c hc
  have hmem : (⟨c, hc⟩ : C) ∈ Subgroup.centralizer (fittingSubgroup C : Set C) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hc (f : X) (hFC ⟨f, hf, rfl⟩)
  exact hFC ⟨⟨c, hc⟩, hCC hmem, rfl⟩


end CFSG.RankThree.PartTwo.Sec4.Census
