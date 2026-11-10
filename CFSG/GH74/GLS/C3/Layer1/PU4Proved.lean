module

public import CFSG.GH74.GLS.C3.Layer1.EvenStd
public import CFSG.LocalAnalysis.ComponentInitial.BlockAschbacherTheorem5
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecChar
import CFSG.GH74.E2.TermBasic
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.LocalAnalysis.StandardType.GGCentralQuotientEq
import CFSG.GH74.Generic.BProg.B1.Stage3aSD2
import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitBasic
public import CFSG.LocalAnalysis.OddStandard.Children
import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG

theorem isQuasisimple_of_isCompIn {G : Type} [Group G] {H K : Subgroup G} (h : IsCompIn H K) :
    CFSG.IsQuasisimple ↥K :=
  (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
    (Subgroup.subgroupOfEquivOfLe h.1).symm).2 h.2.1

theorem isStandardSubgroup_of_componentType {Y : Type*} [Group Y] {J : Subgroup Y}
    (h : CFSG.Assembly.ComponentType.IsStandardSubgroup J) : CFSG.IsStandardSubgroup J :=
  CFSG.StandardSubgroupAPI.isStandardSubgroup_iff_assembly.2 h


theorem b_cor_PU4_proved :
    B_cor_PU4 := by
  intro G _ _ hG x K hx hcomp hrank hterm
  have : IsSimpleGroup G := hG.1
  have hKC : K ≤ centralizer ({x} : Set G) := hcomp.1
  have hq : CFSG.Assembly.IsQuasisimple K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (isQuasisimple_of_isCompIn hterm.2.1)
  have hrk : 2 ≤ CFSG.Assembly.pRank 2 K := by
    have h1 : CFSG.pRank 2 ↥K = CFSG.Open.pRank 2 K :=
      (CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥K).trans
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup K).symm
    have h2 : 2 ≤ CFSG.Open.pRank 2 K := h1 ▸ hrank
    exact h2
  have hxC : x ∈ centralizer (K : Set G) := by
    rw [mem_centralizer_iff]
    intro k hk
    exact mem_centralizer_singleton_iff.1 (hKC hk)
  have hCeven : Even (Nat.card (centralizer (K : Set G))) := by
    have h2 : 2 ∣ Nat.card (centralizer (K : Set G)) := by
      have h3 := orderOf_dvd_natCard (⟨x, hxC⟩ : centralizer (K : Set G))
      have e : orderOf (⟨x, hxC⟩ : centralizer (K : Set G)) = 2 := by
        rw [← hx]
        exact Subgroup.orderOf_mk _ _
      rwa [e] at h3
    exact even_iff_two_dvd.2 h2
  have hU : CFSG.LocalAnalysis.ComponentInitial.IsUniversalComponent K := by
    intro t ht ht2
    have hKt : K ≤ centralizer ({t} : Set G) := by
      intro k hk
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.1 ht) k hk
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hKt).2
      (hterm.2.2.2 t ht2 ht).2
  exact isStandardSubgroup_of_componentType
    (CFSG.LocalAnalysis.ComponentInitial.universal_rank_two_component_isStandardSubgroup
      hG.2.1 hq hrk hCeven hU)


section CertificatesPU4


end CertificatesPU4

end CFSG.GH74.GLS
