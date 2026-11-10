module

public import CFSG.SignalizerFunctorTheorem.Inheritance.CosetFixed

public section

namespace CFSG.SignalizerFunctorTheorem

variable {G : Type*} [Group G] {K L A : Subgroup G}

noncomputable def sectionConjAut (hAK : A ≤ Subgroup.normalizer (K : Set G)) (a : A) :
    MulAut K :=
  K.normalizerMonoidHom ⟨a, hAK a.2⟩

theorem coe_sectionConjAut (hAK : A ≤ Subgroup.normalizer (K : Set G)) (a : A) (k : K) :
    ((sectionConjAut hAK a k : K) : G) = a * k * (a : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe K _ k

theorem sectionConjAut_mem_iff (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (a : A) (k : K) :
    ((sectionConjAut hAK a k : K) : G) ∈ L ↔ (k : G) ∈ L := by
  rw [coe_sectionConjAut]
  exact ((Subgroup.mem_normalizer_iff.mp (hAL a.2)) k).symm

theorem map_sectionConjAut_eq (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (a : A) :
    (L.subgroupOf K).map (sectionConjAut hAK a : K →* K) = L.subgroupOf K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (sectionConjAut_mem_iff hAK hAL a y).mpr hy
  · intro hx
    refine ⟨(sectionConjAut hAK a).symm x, ?_, (sectionConjAut hAK a).apply_symm_apply x⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, ← sectionConjAut_mem_iff hAK hAL a,
      MulEquiv.apply_symm_apply]
    exact hx

variable [(L.subgroupOf K).Normal]

noncomputable def sectionAction (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) : A →* MulAut (K ⧸ L.subgroupOf K) where
  toFun a := QuotientGroup.congr (L.subgroupOf K) (L.subgroupOf K) (sectionConjAut hAK a)
    (map_sectionConjAut_eq hAK hAL a)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H k =>
      rw [QuotientGroup.congr_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [coe_sectionConjAut]
      simp
  map_mul' a b := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H k =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk]
      congr 1
      apply Subtype.ext
      simp only [coe_sectionConjAut, Subgroup.coe_mul]
      group

theorem sectionAction_mk (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (a : A) (k : K) :
    sectionAction hAK hAL a (QuotientGroup.mk k) = QuotientGroup.mk (sectionConjAut hAK a k) :=
  QuotientGroup.congr_mk _ _ _ (map_sectionConjAut_eq hAK hAL a) k

theorem sectionAction_mk_eq_iff (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (a : A) (k : K) :
    sectionAction hAK hAL a (QuotientGroup.mk k) = QuotientGroup.mk k ↔
      (k : G)⁻¹ * (a * k * (a : G)⁻¹) ∈ L := by
  rw [sectionAction_mk, eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_sectionConjAut]


end CFSG.SignalizerFunctorTheorem
