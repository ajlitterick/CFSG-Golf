module

public import CFSG.LocalAnalysis.RankThreeUC.ClauseC
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartOne.S12.Sec15Final
import CFSG.LocalAnalysis.RankThreeTheoremC.WreathThompson
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S10.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]


omit [Finite G] in
private theorem le_of_isPGroup_of_not_dvd_relIndex {p : ℕ} [Fact p.Prime] {M C Q : Subgroup G}
    (hCM : C ≤ M) (hMC : M ≤ normalizer (C : Set G)) (hQM : Q ≤ M) (hQ : IsPGroup p Q)
    (hC : ¬ p ∣ C.relIndex M) : Q ≤ C := by
  have : (C.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hCM).mpr hMC
  intro q hq
  let x : M := ⟨q, hQM hq⟩
  have h1 : orderOf (QuotientGroup.mk' (C.subgroupOf M) x) ∣ orderOf x :=
    orderOf_map_dvd _ _
  have h2 : orderOf (QuotientGroup.mk' (C.subgroupOf M) x) ∣ C.relIndex M :=
    orderOf_dvd_natCard _
  have h3 : (orderOf x).Coprime (C.relIndex M) := by
    have h := hQ.orderOf_coprime ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hC) ⟨q, hq⟩
    rw [Subgroup.orderOf_mk q hq] at h
    rwa [show orderOf x = orderOf q from Subgroup.orderOf_mk q (hQM hq)]
  have h4 : orderOf (QuotientGroup.mk' (C.subgroupOf M) x) = 1 :=
    Nat.Coprime.eq_one_of_dvd (h3.coprime_dvd_left h1) h2
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h4)

omit [Finite G] in
private theorem le_normalizer_inf_centralizer {M Z : Subgroup G}
    (hZ : M ≤ normalizer (Z : Set G)) :
    M ≤ normalizer ((M ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) := by
  have key : ∀ m ∈ M, ∀ h : G, h ∈ M ⊓ centralizer (Z : Set G) →
      m * h * m⁻¹ ∈ M ⊓ centralizer (Z : Set G) := by
    intro m hm h ⟨hhM, hhc⟩
    refine ⟨M.mul_mem (M.mul_mem hm hhM) (M.inv_mem hm), mem_centralizer_iff.mpr fun z hz => ?_⟩
    have hz' : m⁻¹ * z * m ∈ Z := by
      have := (mem_normalizer_iff.mp (hZ (M.inv_mem hm)) z).mp hz
      simpa using this
    have hc := mem_centralizer_iff.mp hhc _ hz'
    calc z * (m * h * m⁻¹) = m * ((m⁻¹ * z * m) * h) * m⁻¹ := by group
      _ = m * (h * (m⁻¹ * z * m)) * m⁻¹ := by rw [hc]
      _ = m * h * m⁻¹ * z := by group
  intro m hm
  refine mem_normalizer_iff.mpr fun h => ⟨key m hm h, fun h' => ?_⟩
  simpa [mul_assoc] using key m⁻¹ (M.inv_mem hm) _ h'


end CFSG.LocalAnalysis.RankThreeUC
