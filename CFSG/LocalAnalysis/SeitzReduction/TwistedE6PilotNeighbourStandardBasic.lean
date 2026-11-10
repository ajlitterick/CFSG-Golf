module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneExceptionalKernel
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6CascadeFinal
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotModel

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section General

variable {M : Type*} [Group M]

theorem centralizer_subgroupOf {A C : Subgroup M} (hAC : A ≤ C) :
    centralizer (A.subgroupOf C : Set C) = (centralizer (A : Set M)).subgroupOf C := by
  ext x
  rw [mem_subgroupOf, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h a ha
    exact congrArg Subtype.val (h ⟨a, hAC ha⟩ (mem_subgroupOf.2 ha))
  · intro h a ha
    exact Subtype.ext (h a (mem_subgroupOf.1 ha))

theorem centralizer_subgroupOf_eq_sup {A Y D C : Subgroup M} (hAC : A ≤ C) (hYC : Y ≤ C)
    (hDC : D ≤ C) (h : centralizer (A : Set M) ⊓ C = Y ⊔ D) :
    centralizer (A.subgroupOf C : Set C) = Y.subgroupOf C ⊔ D.subgroupOf C := by
  rw [centralizer_subgroupOf hAC, ← inf_subgroupOf_right, h, subgroupOf_sup hYC hDC]


theorem map_conj_le_centralizer_map_conj {Y D : Subgroup M} (h : Y ≤ centralizer (D : Set M))
    (n : M) : Y.map (MulAut.conj n).toMonoidHom ≤
      centralizer ((D.map (MulAut.conj n).toMonoidHom : Subgroup M) : Set M) :=
  F4Pilot.map_le_centralizer_map _ h

theorem isQuasisimple_subgroupOf {D C : Subgroup M} (hDC : D ≤ C) [IsSimpleGroup D]
    [Group.IsPerfect D] : CFSG.IsQuasisimple (D.subgroupOf C) := by
  have hnc : ∃ a b : D, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isMulCommutative D ⟨⟨fun a b => h a b⟩⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hDC).symm
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1


end General

section Kernel


theorem lieModel_quotient_center_twistedE6 {L : Type} [Group L] (hZ : center L = ⊥) {f : ℕ}
    (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) :
    LieModel (L ⧸ center L) .twistedE6 0 2 f := by
  have := finite_of_card hK
  obtain ⟨e'⟩ := RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv TwistTag.E6
    Nat.prime_two hf K hK σ hσ
  exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hf, rfl⟩, K, inferInstance,
    inferInstance, hK, σ, hσ, ⟨(quotientCenterMulEquiv hZ).trans (e.trans e'.symm)⟩⟩)


theorem inf_centralizer_eq_zpowers_twistedE6 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : SeitzSetting G L) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
  inf_centralizer_eq_zpowers_of_exceptional exceptionalHypothesisOne hset.standardSetting
    hset.center_eq_bot (Or.inr (Or.inr (Or.inl rfl)))
    (lieModel_quotient_center_twistedE6 hset.center_eq_bot hf hK hσ e) htC ht

end Kernel

section Generic

variable {G : Type*} [Group G] {L : Subgroup G} {C : Type*} [Group C]

theorem forall_fix_eq_one_map_symm (e : L ≃* C) {A D : Subgroup C}
    (hAut : ∀ β : MulAut C, (∀ x ∈ A, β x = x) → (∀ x ∈ D, β x = x) →
      ∀ n : ℕ, β ^ 2 ^ n = 1 → β = 1) :
    ∀ β : MulAut L, (∀ a : L, (a : G) ∈ (A.map e.symm.toMonoidHom).map L.subtype → β a = a) →
      (∀ a : L, (a : G) ∈ (D.map e.symm.toMonoidHom).map L.subtype → β a = a) →
      ∀ n : ℕ, β ^ 2 ^ n = 1 → β = 1 := by
  intro β hβX hβD n hβn
  have hmem : ∀ {B : Subgroup C} {x : C}, x ∈ B →
      ((e.symm x : L) : G) ∈ (B.map e.symm.toMonoidHom).map L.subtype :=
    fun {_ x} hx => ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩
  have key : MulAut.congr e β = 1 := by
    refine hAut _ (fun x hx => ?_) (fun x hx => ?_) n ?_
    · rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hβX _ (hmem hx),
        MulEquiv.apply_symm_apply]
    · rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hβD _ (hmem hx),
        MulEquiv.apply_symm_apply]
    · rw [← map_pow, hβn, map_one]
  have := congrArg (MulAut.congr e).symm key
  rwa [MulEquiv.symm_apply_apply, map_one] at this

theorem isQuasisimple_map_symm (e : L ≃* C) {D : Subgroup C} (hD : CFSG.IsQuasisimple D) :
    CFSG.IsQuasisimple ((D.map e.symm.toMonoidHom).map L.subtype) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((D.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      ((D.map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective)) hD

theorem neighbour_standard_of_centralizer_eq_sup_gen [Finite G]
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* C) {A Y DC : Subgroup C} (hA : centralizer (A : Set C) = Y ⊔ DC)
    (hYD : Y ≤ centralizer (DC : Set C)) (hYc : Y ≤ centralizer (Y : Set C))
    (hDq : CFSG.IsQuasisimple DC)
    (hAut : ∀ β : MulAut C, (∀ x ∈ A, β x = x) → (∀ x ∈ DC, β x = x) →
      ∀ n : ℕ, β ^ 2 ^ n = 1 → β = 1)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = (DC.map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  subst hX hDe
  have hD := F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e hA hYD hYc hDq
  have hDq' := isQuasisimple_map_symm e hDq
  exact F4Pilot.standard_inheritance_of_forall_fix_eq_one hL htC ht hK htX hD.symm
    ⟨hDq'.1.commutator_eq_top, hDq'.2.1⟩ (forall_fix_eq_one_map_symm e hAut)

end Generic

end CFSG.SeitzReduction.TwistedE6Pilot
