module

public import CFSG.ClassicalInvolution.RouteD.TWZLink
public import CFSG.ClassicalInvolution.RouteD.TWSReduce

public section

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

section Sp

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}
  {a : ℕ}


theorem ne_of_mem_range (hP1 : LocalOddCentral Ω {x})
    (Λ : SpLayer p f a Ω x) {M K : Subgroup G} (hM : M ∈ centralizingMembers Ω {x})
    (hMi : locImg Ω x M ≤ (Λ.D.hom Λ.i₁).range) (hK : K ∈ Ω)
    (hz : IsClassicalMember p f K x) (h5 : 5 ≤ p ^ f) : M ≠ K := by
  rintro rfl
  obtain ⟨j, hj, hKj⟩ := SpLayer.exists_other_of_self h5 hK hz Λ
  have h2 : ∀ w ∈ locImg Ω x M, w ∈ Subgroup.center (locQuot Ω x) := fun w hw =>
    range_inf_le_center Λ.D hj ⟨hKj hw, hMi hw⟩
  have hc : Commutes (locImg Ω x M) (locImg Ω x M) := fun u hu v _ =>
    (Subgroup.mem_center_iff.mp (h2 u hu) v).symm
  exact not_commutes_self_of_isClassicalMember hz
    (commutes_of_commutes_locImg_perfect hP1 (le_centralizingLayer hM) (le_centralizingLayer hM)
      (commutator_eq_of_isClassicalMember hz).ge hc)

end Sp

section Linked

variable (p f : ℕ) [Fact p.Prime]


theorem twinYLinkedSp2 : TWS.TwinYLinkedSp2 p f := by
  intro G _ _ _ hnab K z S hshape Λ K₂ hK₂ hK₂Λ w hw hex
  obtain ⟨T, e, hT, clsT, hP1, hty⟩ := hex
  have hrow : TwinRow .PSp 2 := Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  have hMF : TwinMFGeneration p f .PSp 2 := twinMFGeneration_psp2 S.odd (le_trans (by norm_num : 3 ≤ 5) S.five)
  have hK₂K : K₂ ≠ K := ne_of_mem_range S.p1 Λ hK₂ hK₂Λ
    (CoreAssembly.mem_conjClass_self K) S.cls S.five
  have hK₂T : K₂ ≠ T := ne_of_mem_range S.p1 Λ hK₂ hK₂Λ hT.mem.1 clsT S.five
  obtain ⟨D, hcard, i, ht, hr, -⟩ := hty
  have hcard1 : D.card = 1 := by omega
  have ht' : D.tag i = .POmegaOdd := ht
  have hr' : D.rank i = 3 := hr
  have hDi : D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
    rw [ht']
    exact ⟨by decide, by decide⟩
  have hnc : ¬ (D.tag i = .PSL ∧ D.rank i = 2) := by
    rintro ⟨h1, -⟩
    rw [ht'] at h1
    exact absurd h1 (by decide)
  obtain ⟨hexp, -, -, -⟩ := component_package S.odd S.five D hcard1 i hDi
  have hmodel : SqTrichotomyOn (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out) := by
    have hadm := D.admissible i
    rw [ht', hr', hexp] at hadm ⊢
    exact sqTrichotomy_odd3 S.odd S.five hadm
  exact linked_of_model hnab S hrow hshape hT clsT e hMF hP1 D hcard1 i hDi hnc hmodel hK₂ hK₂K
    hK₂T hw

end Linked

end CFSG.ClassicalInvolution.RouteD.TWZ
