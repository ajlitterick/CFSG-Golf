module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveTypeA
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNodeAut
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNodeRel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.RankThree.PartTwo.Sec21 Matrix SpecialLinear

section Config

variable {G : Type} [Group G] [Finite G]

@[expose] def GGTypeASplitNbr (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (n f : ℕ)
    (y : G) (K : Subgroup G) : Prop :=
  GGConfig p B Bs x L D J ∧ GGOpAutTrivial p Bs ∧ GGInnerDiagAll p B Bs x L D J ∧
    GGNoTransvection p Bs ∧
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSL (n + 1) 2 f ∧ p ∣ 2 ^ f - 1 ∧ 3 ≤ n ∧
    ¬ p ∣ n + 3 ∧ GGScalarsPmOne Bs ∧ GGNbr p B x D J y K ∧
    StatedClassicalModel (K ⧸ Subgroup.center K) .PSL (n + 1) 2 f ∧
    (∃ e : (CoxeterMatrix.A (n + 1)).Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs),
      ∀ i, GGIsReflection p ((e ((CoxeterMatrix.A (n + 1)).simple i) :
        ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs)) ∧
    GGSecFiveAllAJoin p B Bs x L D J

theorem exists_ggTypeASplitNbr {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (hA : GGTypeASplitConfig p B Bs x L D J n f) :
    ∃ (y : G) (K : Subgroup G), GGTypeASplitNbr p B Bs x L D J n f y K := by
  obtain ⟨hmod, hpq, hn, hp3, hsc, y, K, hnbr, hmodK, hW, hgate⟩ := hA
  exact ⟨y, K, hcfg, hOp, hInn, hNoTr, hmod, hpq, hn, hp3, hsc, hnbr, hmodK, hW, hgate⟩

end Config


@[expose] def GGTypeAJoinInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeASplitNbr p B Bs x L D J n f y K →
    ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' → K' ≤ L ⊔ K

section Lifts

variable {n : ℕ} {F : Type} [Field F] {X : Type*} [Group X]

theorem range_mulAutConj_comp {H : Subgroup X} {l : X} (hl : l ∈ H)
    {φ : SpecialLinearGroup (Fin (n + 1)) F →* X} (hφ : φ.range = H) :
    ((MulAut.conj l).toMonoidHom.comp φ).range = H := by
  rw [MonoidHom.range_comp, hφ]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hl)

theorem ker_mulAutConj_comp (l : X) (φ : SpecialLinearGroup (Fin (n + 1)) F →* X) :
    ((MulAut.conj l).toMonoidHom.comp φ).ker = φ.ker := by
  ext g
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · intro h
    calc φ g = l⁻¹ * (l * φ g * l⁻¹) * l := by group
      _ = 1 := by rw [h]; group
  · intro h
    rw [h]
    group

theorem GGTypeAEndNode.of_conj {φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X} {l T : X}
    (h : GGTypeAEndNode ((MulAut.conj l).toMonoidHom.comp φ₁) T) :
    GGTypeAEndNode φ₁ (l⁻¹ * T * l) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h2 h3
  refine ⟨?_, ?_, ?_⟩
  · calc l⁻¹ * T * l * (l⁻¹ * T * l) = l⁻¹ * (T * T) * l := by group
      _ = 1 := by rw [h1]; group
  · intro j hj
    have e : l⁻¹ * T * l * φ₁ (weylRep n F j) =
        l⁻¹ * (T * (l * φ₁ (weylRep n F j) * l⁻¹)) * l⁻¹⁻¹ := by group
    rw [e, conj_pow, h2 j hj]
    group
  · intro a b hab ha hb c
    have e := h3 a b hab ha hb c
    calc l⁻¹ * T * l * φ₁ (Matrix.SpecialLinearGroup.transvection hab c)
        = l⁻¹ * (T * (l * φ₁ (Matrix.SpecialLinearGroup.transvection hab c) * l⁻¹)) * l := by
          group
      _ = l⁻¹ * ((l * φ₁ (Matrix.SpecialLinearGroup.transvection hab c) * l⁻¹) * T) * l := by
          rw [e]
      _ = φ₁ (Matrix.SpecialLinearGroup.transvection hab c) * (l⁻¹ * T * l) := by group

theorem injective_comp_slLowerBlockHom {φ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F)) :
    Function.Injective (φ.comp (slLowerBlockHom n F)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  exact eq_one_of_slLowerBlockHom_mem_center (hker hg)

theorem injective_comp_slUpperBlockHom {φ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F)) :
    Function.Injective (φ.comp (slUpperBlockHom n F)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  exact eq_one_of_slUpperBlockHom_mem_center (hker hg)

theorem exists_slCompat_lift [Finite F] (hn : 3 ≤ n)
    {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker₁ : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hker₂ : φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hJ : (φ₁.comp (slLowerBlockHom n F)).range = (φ₂.comp (slUpperBlockHom n F)).range) :
    ∃ φ₂' : SpecialLinearGroup (Fin (n + 1)) F →* X, φ₂'.range = φ₂.range ∧
      φ₂'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F) ∧
      φ₁.comp (slLowerBlockHom n F) = φ₂'.comp (slUpperBlockHom n F) := by
  have hθ₁ := injective_comp_slLowerBlockHom hker₁
  have hθ₂ := injective_comp_slUpperBlockHom hker₂
  let β : MulAut (SpecialLinearGroup (Fin n) F) :=
    ((MonoidHom.ofInjective hθ₁).trans (MulEquiv.subgroupCongr hJ)).trans
      (MonoidHom.ofInjective hθ₂).symm
  have hβ : ∀ g, φ₂ (slUpperBlockHom n F (β g)) = φ₁ (slLowerBlockHom n F g) := by
    intro g
    have e := MulEquiv.apply_symm_apply (MonoidHom.ofInjective hθ₂)
      ((MulEquiv.subgroupCongr hJ) (MonoidHom.ofInjective hθ₁ g))
    have e' := congrArg Subtype.val e
    rw [MonoidHom.ofInjective_apply] at e'
    exact e'.trans (by rw [MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]; rfl)
  obtain ⟨β', hβ'⟩ := exists_mulAut_slUpperBlockHom hn β
  refine ⟨φ₂.comp β'.toMonoidHom, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr β'.surjective, ← MonoidHom.range_eq_map]
  · intro g hg
    have hc : β' g ∈ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F) := hker₂ hg
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro h
    apply β'.injective
    rw [map_mul, map_mul]
    exact hc (β' h)
  · ext g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hβ', hβ]

end Lifts


end CFSG.StandardType
