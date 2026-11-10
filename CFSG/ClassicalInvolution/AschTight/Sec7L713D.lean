module

public import CFSG.ClassicalInvolution.AschTight.Sec7L713C
public import CFSG.ClassicalInvolution.AschTight.Sec7L713A

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G]

instance normal_sup_OCW_subgroupOf (W : Subgroup G) :
    ((W ⊔ OCW W).subgroupOf (Subgroup.normalizer (W : Set G))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (sup_le Subgroup.le_normalizer (OCW_le_normalizer W))).mpr
    (normalizer_le_normalizer_sup_OCW W)

abbrev NBar (W : Subgroup G) : Type :=
  ↥(Subgroup.normalizer (W : Set G)) ⧸ (W ⊔ OCW W).subgroupOf (Subgroup.normalizer (W : Set G))

abbrev bar {W : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (W : Set G)) : NBar W :=
  QuotientGroup.mk (⟨g, hg⟩ : ↥(Subgroup.normalizer (W : Set G)))

variable {W : Subgroup G}


theorem bar_eq_one_iff {g : G} (hg : g ∈ Subgroup.normalizer (W : Set G)) :
    bar hg = 1 ↔ g ∈ W ⊔ OCW W := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem bar_eq_iff {g h : G} (hg : g ∈ Subgroup.normalizer (W : Set G))
    (hh : h ∈ Subgroup.normalizer (W : Set G)) : bar hg = bar hh ↔ g⁻¹ * h ∈ W ⊔ OCW W := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

variable {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem bar_of_mem_DSet (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) (h611 : EtaMeets Ω)
    (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) {r : G} (hrR : r ∈ R) (hrW : r ∉ W) :
    (∀ ρ (hρ : ρ ∈ R), bar (hR.2 hρ) = 1 ∨ bar (hR.2 hρ) = bar (hR.2 hrR)) ∧
      bar (hR.2 hrR) ≠ 1 ∧ bar (hR.2 hrR) * bar (hR.2 hrR) = 1 := by
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR.1
  obtain ⟨-, -, hcard, -⟩ := inf_W_of_mem_DSet hp hΩ h611 hW hR hJ hRJ.1
  have h2 := relIndex_eq_two_of_card (inf_le_left : R ⊓ W ≤ R) hcard
  have hrA : r ∉ R ⊓ W := fun h => hrW (Subgroup.mem_inf.mp h).2
  have hR2 := isPGroup_of_mem_RSet hR.1
  have hW2 := isPGroup_of_mem_WSet hW
  refine ⟨fun ρ hρ => ?_, fun h => ?_, ?_⟩
  · rcases mem_or_mul_inv_mem_of_relIndex_two h2 hrR hrA hρ with h | h
    · exact Or.inl ((bar_eq_one_iff _).mpr (Subgroup.mem_sup_left (Subgroup.mem_inf.mp h).2))
    · right
      have h1 : bar (Subgroup.mul_mem _ (hR.2 hρ) (Subgroup.inv_mem _ (hR.2 hrR))) = 1 :=
        (bar_eq_one_iff _).mpr (Subgroup.mem_sup_left (Subgroup.mem_inf.mp h).2)
      change bar (hR.2 hρ) * (bar (hR.2 hrR))⁻¹ = 1 at h1
      exact mul_inv_eq_one.mp h1
  · rw [bar_eq_one_iff] at h
    exact hrW (mem_of_isPGroup_of_mem_sup_OCW hW2 h (hR2.to_le (Subgroup.zpowers_le.mpr hrR)))
  · change bar (Subgroup.mul_mem _ (hR.2 hrR) (hR.2 hrR)) = 1
    rw [bar_eq_one_iff]
    exact Subgroup.mem_sup_left (Subgroup.mem_inf.mp (mul_self_mem_of_relIndex_two h2 hrR)).2

omit [Finite G] in
theorem mem_sup_of_bar_eq {R : Subgroup G} {g h : G} (hgR : g ∈ R)
    (hg : g ∈ Subgroup.normalizer (W : Set G)) (hh : h ∈ Subgroup.normalizer (W : Set G))
    (he : bar hg = bar hh) : h ∈ R ⊔ W ⊔ OCW W := by
  rw [bar_eq_iff] at he
  have e : h = g * (g⁻¹ * h) := by group
  rw [e, sup_assoc]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hgR) (Subgroup.mem_sup_right he)

theorem le_sup_of_bar_eq (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) (h611 : EtaMeets Ω)
    (hW : W ∈ WSet Ω) {R T : Subgroup G} (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) {r t : G}
    (hrR : r ∈ R) (htT : t ∈ T) (htW : t ∉ W) (he : bar (hT.2 htT) = bar (hR.2 hrR)) :
    T ≤ R ⊔ W ⊔ OCW W := by
  obtain ⟨hT1, -, -⟩ := bar_of_mem_DSet hp hΩ h611 hW hT htT htW
  intro τ hτ
  rcases hT1 τ hτ with h | h
  · rw [bar_eq_one_iff] at h
    rw [sup_assoc]
    exact Subgroup.mem_sup_right h
  · exact mem_sup_of_bar_eq hrR (hR.2 hrR) (hT.2 hτ) (h.trans he).symm


end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
