module

public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Quasithin.Background.D2Thirteen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PSubgroupInfNormalNilpotentLePCore

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

section Abstract

theorem exists_isComponentOf_not_le_centralizer {Q : Type} [Group Q] [Finite Q]
    {A : Subgroup Q} (hA2 : IsPGroup 2 ↥A) (hO2 : CFSG.pCore 2 Q = ⊥) (hAne : A ≠ ⊥)
    (hF : ∀ p : (Nat.card Q).primeFactors, CFSG.pCore (p : ℕ) Q ≤
      Subgroup.centralizer (A : Set Q)) :
    ∃ E : Subgroup Q, CFSG.GorensteinWalter.IsComponentOf E ⊤ ∧
      ¬ A ≤ Subgroup.centralizer (E : Set Q) := by
  classical
  by_contra hall
  push Not at hall
  have hFeq : CFSG.fittingSubgroupOf (⊤ : Subgroup Q) = CFSG.fittingSubgroup Q :=
    CFSG.Adapters.fittingSubgroupOf_top_eq_foundations Q
  have hFeqGW : CFSG.GorensteinWalter.fittingSubgroupOf (⊤ : Subgroup Q) = CFSG.fittingSubgroup Q :=
    hFeq
  have hFA : CFSG.fittingSubgroup Q ≤ Subgroup.centralizer (A : Set Q) := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    exact iSup_le hF
  have hEA : CFSG.GorensteinWalter.componentLayerOf (⊤ : Subgroup Q) ≤
      Subgroup.centralizer (A : Set Q) :=
    sSup_le fun E hE => Subgroup.le_centralizer_iff.mp (hall E hE)
  have hXA : CFSG.GorensteinWalter.generalizedFittingSubgroupOf (⊤ : Subgroup Q) ≤
      Subgroup.centralizer (A : Set Q) := by
    unfold CFSG.GorensteinWalter.generalizedFittingSubgroupOf
    rw [hFeqGW]
    exact sup_le hFA hEA
  have hAC := Subgroup.le_centralizer_iff.mpr hXA
  have hAX := hAC.trans CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le
  have hAF : A ≤ CFSG.fittingSubgroup Q := by
    rw [← hFeqGW]
    exact (le_inf hAC hAX).trans
      CFSG.GorensteinWalter.centralizer_generalizedFitting_intersection_le_fittingSubgroupOf
  have hAO := (le_inf le_rfl hAF).trans
    (CFSG.GorensteinWalter.pSubgroup_inf_normal_nilpotent_le_pCore A (CFSG.fittingSubgroup Q) 2
      Nat.prime_two hA2 CFSG.fittingSubgroup_normal CFSG.fittingSubgroup_nilpotent)
  rw [hO2, le_bot_iff] at hAO
  exact hAne hAO

variable {G : Type*} [Group G]

theorem mem_cComp_of_isQuasisimple_of_isSubnormal {K X : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥K) (hK : IsSubnormal K X) : K ∈ cComp X := by
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hq.1
  refine ⟨?_, hperf, hK, ?_⟩
  · intro hb
    have := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot K).mp this hb
  · intro K' hlt hne hperf' hsub
    have hKX : K ≤ X := A3.subnormal_le hK
    have hsubK : IsSubnormal K' K := A3.subnormal_of_le_of_le hsub hlt.le hKX
    obtain ⟨P, hPK, hPn, hK'P⟩ := A3.subnormal_exists_normal_of_lt hsubK hlt
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hPn with h1 | h1
    · exact absurd (Subgroup.subgroupOf_eq_top.mp h1) (not_le_of_gt hPK)
    · apply hne
      rw [← hperf', Subgroup.commutator_eq_bot_iff_le_centralizer.mpr]
      intro x hx
      have hxP : x ∈ P := hK'P hx
      have hxc := Subgroup.mem_center_iff.mp
        (h1 (show (⟨x, hPK.le hxP⟩ : ↥K) ∈ P.subgroupOf K from hxP))
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      exact congrArg Subtype.val (hxc ⟨y, hlt.le hy⟩)

theorem isQuasisimple_of_gw {Q : Type*} [Group Q] (h : CFSG.GorensteinWalter.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨hnt, hcomm, hs⟩ := h
  refine ⟨Group.isPerfect_def.mpr hcomm, hs, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center Q), _root_.commutator_def,
      ← Subgroup.map_eq_bot_iff, Subgroup.map_commutator, eq_bot_iff]
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, -, b, -, rfl⟩ := hy
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hab a b
    | one => exact Subgroup.one_mem _
    | mul x y _ _ hx hy => exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => exact Subgroup.inv_mem _ hx
  rw [hcomm] at hle
  have htriv : ∀ q : Q ⧸ Subgroup.center Q, q = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [QuotientGroup.eq_one_iff]
    exact hle trivial
  obtain ⟨a, b, hne⟩ := hs.exists_pair_ne
  exact hne ((htriv a).trans (htriv b).symm)

section Offender


end Offender

end Abstract

end CFSG.Quasithin.H13
