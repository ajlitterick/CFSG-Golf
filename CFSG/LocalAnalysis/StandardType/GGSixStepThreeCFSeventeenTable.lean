module

public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFSeventeen
public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.Adapters.LinearSmallCatalog

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Central

theorem ggCenterQuotEquiv_of_surjective {P Q : Type*} [Group P] [Group Q]
    (hP : Group.IsPerfect P) (f : P →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center P) :
    Nonempty (P ⧸ Subgroup.center P ≃* Q ⧸ Subgroup.center Q) := by
  have hc : Subgroup.center P = ((QuotientGroup.mk' (Subgroup.center Q)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      CFSG.LocalCores.comap_center_eq_of_perfect hP f hf hker]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))⟩

theorem ggLieModel_psl_two_four_of_alt {Y : Type} [Group Y]
    (e : Y ≃* alternatingGroup (Fin 5)) : LieModel Y .PSL 2 2 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl (by rw [hK]; norm_num))
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, by decide⟩, GaloisField 2 2,
    inferInstance, inferInstance, hK, ⟨e.trans e5.symm⟩⟩

end Central

section Image

variable {G : Type} [Group G]

theorem ggAutK_image_component {E₀ K M C L₁ : Subgroup G} (hL₁ : IsComponentOf L₁ C)
    (hL₁K : L₁ ≤ K) (hL₁M : L₁ ≤ M) (hH₀C : E₀ ⊔ (K ⊓ M) ≤ C) (hKq : CFSG.Assembly.IsQuasisimple ↥K)
    (hEK : E₀ ≤ Subgroup.normalizer (K : Set G)) {W' : Type} [Group W'] [Finite W']
    (π : ↥(E₀ ⊔ K) →* W') (hπ : Function.Surjective π)
    (hker : π.ker ≤ ((E₀ ⊔ (K ⊓ M)) ⊓ Subgroup.centralizer (K : Set G)).subgroupOf (E₀ ⊔ K)) :
    IsComponentOf ((L₁.subgroupOf (E₀ ⊔ K)).map π)
        (((E₀ ⊔ (K ⊓ M)).subgroupOf (E₀ ⊔ K)).map π ⊓ CFSG.generalizedFitting W') ∧
      Nonempty (↥L₁ ⧸ Subgroup.center ↥L₁ ≃*
        ↥((L₁.subgroupOf (E₀ ⊔ K)).map π) ⧸
          Subgroup.center ↥((L₁.subgroupOf (E₀ ⊔ K)).map π)) := by
  have hL₁H₀ : L₁ ≤ E₀ ⊔ (K ⊓ M) := (le_inf hL₁K hL₁M).trans le_sup_right
  have hcomp : IsComponentOf L₁ (E₀ ⊔ (K ⊓ M)) :=
    ⟨hL₁H₀, ggIsSubnormal_of_le_of_le hL₁.2.1 hL₁H₀ hH₀C, hL₁.2.2⟩
  have hH₀W₀ : E₀ ⊔ (K ⊓ M) ≤ E₀ ⊔ K := sup_le_sup_left inf_le_left E₀
  have hcomp' := ggIsComponentOf_subgroupOf hcomp hH₀W₀
  have hkerC : ∀ w : ↥(E₀ ⊔ K), π w = 1 → (w : G) ∈ Subgroup.centralizer (K : Set G) :=
    fun w hw => (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp (hker hw))).2
  have hnotker : ¬ L₁.subgroupOf (E₀ ⊔ K) ≤ π.ker := by
    intro hle
    refine ggComponent_not_commute hL₁ fun a ha c hc => ?_
    have haW : a ∈ E₀ ⊔ K := (hL₁K.trans le_sup_right) ha
    have haC := hkerC ⟨a, haW⟩ (hle (Subgroup.mem_subgroupOf.mpr ha :
      (⟨a, haW⟩ : ↥(E₀ ⊔ K)) ∈ L₁.subgroupOf (E₀ ⊔ K)))
    exact (Subgroup.mem_centralizer_iff.mp haC c (hL₁K hc)).symm
  have hcompH := ggIsComponentOf_map π hcomp' hnotker
  have hKW : K ≤ E₀ ⊔ K := le_sup_right
  have hKn : (K.subgroupOf (E₀ ⊔ K)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKW]
    intro h k hh hk
    have hkN : k ∈ Subgroup.normalizer (K : Set G) := (sup_le hEK Subgroup.le_normalizer) hk
    exact (Subgroup.mem_normalizer_iff.mp hkN h).mp hh
  have hKcW : IsComponentOf K (E₀ ⊔ K) := ⟨hKW, ggIsSubnormal_of_normal hKW hKn, hKq⟩
  have hKcomp : CFSG.IsComponent (K.subgroupOf (E₀ ⊔ K)) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hKW).mp hKcW
  have hKnotker : ¬ K.subgroupOf (E₀ ⊔ K) ≤ π.ker := by
    intro hle
    refine ggComponent_not_commute hKcW fun a ha c hc => ?_
    have haC := hkerC ⟨a, hKW ha⟩ (hle (Subgroup.mem_subgroupOf.mpr ha :
      (⟨a, hKW ha⟩ : ↥(E₀ ⊔ K)) ∈ K.subgroupOf (E₀ ⊔ K)))
    exact (Subgroup.mem_centralizer_iff.mp haC c hc).symm
  have hKbar : CFSG.IsComponent ((K.subgroupOf (E₀ ⊔ K)).map π) :=
    ⟨CFSG.LocalCores.isQuasisimple_map hKcomp.1 π hKnotker, (hKn.map π hπ).isSubnormal⟩
  have hKF : (K.subgroupOf (E₀ ⊔ K)).map π ≤ CFSG.generalizedFitting W' :=
    (CFSG.LocalCores.component_le_layer hKbar).trans le_sup_right
  have hLK : (L₁.subgroupOf (E₀ ⊔ K)).map π ≤ (K.subgroupOf (E₀ ⊔ K)).map π :=
    Subgroup.map_mono fun w hw =>
      Subgroup.mem_subgroupOf.mpr (hL₁K (Subgroup.mem_subgroupOf.mp hw))
  have hle : (L₁.subgroupOf (E₀ ⊔ K)).map π ≤
      ((E₀ ⊔ (K ⊓ M)).subgroupOf (E₀ ⊔ K)).map π ⊓ CFSG.generalizedFitting W' :=
    le_inf hcompH.1 (hLK.trans hKF)
  refine ⟨⟨hle, ggIsSubnormal_of_le_of_le hcompH.2.1 hle inf_le_left, hcompH.2.2⟩, ?_⟩
  have hL₁W : L₁ ≤ E₀ ⊔ K := hL₁K.trans le_sup_right
  set φ : ↥L₁ →* W' := π.comp (Subgroup.inclusion hL₁W)
  have hφmem : ∀ l : ↥L₁, φ l ∈ (L₁.subgroupOf (E₀ ⊔ K)).map π := fun l =>
    ⟨Subgroup.inclusion hL₁W l, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
  set φ' : ↥L₁ →* ↥((L₁.subgroupOf (E₀ ⊔ K)).map π) := φ.codRestrict _ hφmem
  have hφ' : Function.Surjective φ' := by
    rintro ⟨y, w, hw, rfl⟩
    refine ⟨⟨(w : G), Subgroup.mem_subgroupOf.mp hw⟩, Subtype.ext ?_⟩
    rfl
  have hkerφ : φ'.ker ≤ Subgroup.center ↥L₁ := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have h1 : π (Subgroup.inclusion hL₁W l) = 1 := congrArg Subtype.val hl
    have hlC := hkerC _ h1
    rw [Subgroup.mem_center_iff]
    intro l'
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hlC l' (hL₁K l'.2))
  have hperf : Group.IsPerfect ↥L₁ :=
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hL₁.2.2).1
  exact ggCenterQuotEquiv_of_surjective hperf φ' hφ' hkerφ

end Image

section Table

theorem ggSixSeventeen_not_fusionException {G : Type} [Group G]
    {p : ℕ} {t : StatedLieTag} {f : ℕ} {L₁ : Subgroup G} (hnex : ¬ GGSixSeventeenExcluded p t f L₁)
    {W' : Type} [Group W'] [Finite W'] {H E C : Subgroup W'}
    (hC : IsComponentOf C (H ⊓ CFSG.generalizedFitting W'))
    (he : Nonempty (↥L₁ ⧸ Subgroup.center ↥L₁ ≃* ↥C ⧸ Subgroup.center ↥C)) :
    ¬ GGFusionException p H E := by
  obtain ⟨e⟩ := he
  rintro (⟨-, -, hnc⟩ | ⟨hp5, -, hall⟩ |
      ⟨-, ⟨hp3, -, hall⟩ | ⟨hp3, -, hall⟩ | ⟨hp3, -, hall⟩ | ⟨-, -, hnc⟩ | ⟨-, -, hnc⟩⟩ |
      ⟨hp5, -, hall⟩)
  · exact hnc C hC
  · obtain ⟨e5⟩ := hall C hC
    exact hnex (Or.inr (Or.inl ⟨hp5, Or.inl (ggLieModel_psl_two_four_of_alt (e.trans e5))⟩))
  · exact hnex (Or.inl ⟨hp3, Or.inr (Or.inr (lieModel_of_mulEquiv' e.symm (hall C hC)))⟩)
  · exact hnex (Or.inl ⟨hp3, Or.inl (lieModel_of_mulEquiv' e.symm (hall C hC))⟩)
  · obtain ⟨e6⟩ := hall C hC
    exact hnex (Or.inl ⟨hp3, Or.inr (Or.inl ⟨e.trans e6⟩)⟩)
  · exact hnc C hC
  · exact hnc C hC
  · exact hnex (Or.inr (Or.inl ⟨hp5, Or.inr (lieModel_of_mulEquiv' e.symm (hall C hC))⟩))

end Table

section Inputs


end Inputs

end CFSG.StandardType
