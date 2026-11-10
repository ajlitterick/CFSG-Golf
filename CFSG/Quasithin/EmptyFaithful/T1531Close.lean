module

public import CFSG.Quasithin.EmptyFaithful.T1531Line
public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.Quasithin.EmptyFaithful.S143Aux
public import CFSG.GroupTheory.KleinFourAutomorphism

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise


section Solvable

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem isSolvable_Y153 (h1 : Case157One T Mc M) : Group.IsSolvable ↥(Y153 Mc M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := h1.2
  have hQp : IsPGroup 2 ↥(Open.pCore 2 ↥(Y153 Mc M)) :=
    CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥(Y153 Mc M)) 2
  have : Group.IsNilpotent ↥(Open.pCore 2 ↥(Y153 Mc M)) := hQp.isNilpotent
  have hQ : Group.IsSolvable ↥(Open.pCore 2 ↥(Y153 Mc M)) := inferInstance
  have hquot : Group.IsSolvable (OTwoQuot (Y153 Mc M)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact Group.isSolvable_of_ker_le_range (Open.pCore 2 ↥(Y153 Mc M)).subtype
    (QuotientGroup.mk' (Open.pCore 2 ↥(Y153 Mc M))) (by simp [QuotientGroup.ker_mk'])

theorem isSolvable_M153 {t : G} {V₁ V₂ : Subgroup G} (c : Ctx153 G T Mc M V₁ V₂ t)
    (h1 : Case157One T Mc M) (hM : M = Y153 Mc M ⊔ T) : Group.IsSolvable ↥M := by
  have hYM := Y153_le Mc M
  have hTY : T ≤ Subgroup.normalizer (Y153 Mc M : Set G) := c.hyp.T_le.trans (le_normalizer_Y153 Mc M)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYs : Group.IsSolvable ↥(Y153 Mc M) := isSolvable_Y153 h1
  have hNn : ((Y153 Mc M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mpr (le_normalizer_Y153 Mc M)
  have hNs : Group.IsSolvable ↥((Y153 Mc M).subgroupOf M) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hYM).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYM).injective
  have hTp : IsPGroup 2 ↥T := c.hyp.qtfe.sylow.1
  have : Group.IsNilpotent ↥T := hTp.isNilpotent
  have hTs : Group.IsSolvable ↥T := inferInstance
  let φ : ↥T →* ↥M ⧸ (Y153 Mc M).subgroupOf M :=
    (QuotientGroup.mk' ((Y153 Mc M).subgroupOf M)).comp (Subgroup.inclusion c.hyp.T_le)
  have hφ : Function.Surjective φ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      have hx : (x : G) ∈ Y153 Mc M ⊔ T := (SetLike.ext_iff.mp hM (x : G)).mp x.2
      have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (Y153 Mc M) T hTY
      have hx' : (x : G) ∈ (Y153 Mc M : Set G) * (T : Set G) := by rw [← hmul]; exact hx
      obtain ⟨y, hy, τ, hτ, hyτ⟩ := Set.mem_mul.mp hx'
      refine ⟨⟨τ, hτ⟩, ?_⟩
      have hxe : x = ⟨y, hYM hy⟩ * ⟨τ, c.hyp.T_le hτ⟩ := Subtype.ext hyτ.symm
      show QuotientGroup.mk (⟨τ, c.hyp.T_le hτ⟩ : ↥M) = QuotientGroup.mk x
      rw [hxe, QuotientGroup.mk_mul]
      have h1 : (QuotientGroup.mk (⟨y, hYM hy⟩ : ↥M) : ↥M ⧸ (Y153 Mc M).subgroupOf M) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hy
      rw [h1, one_mul]
  have hquot : Group.IsSolvable (↥M ⧸ (Y153 Mc M).subgroupOf M) := Group.isSolvable_of_surjective hφ
  exact Group.isSolvable_of_ker_le_range ((Y153 Mc M).subgroupOf M).subtype
    (QuotientGroup.mk' ((Y153 Mc M).subgroupOf M))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end Solvable

section Geometry

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem TE153_le_normalizer_YE153 (c : Ctx153 G T Mc M V₁ V₂ t) :
    TE153 T E ≤ Subgroup.normalizer (YE153 Mc M E : Set G) := by
  intro τ hτ
  have h1 : τ ∈ Subgroup.normalizer
      ((Y153 Mc M ⊓ Subgroup.normalizer (E : Set G) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_Y153 Mc M (c.hyp.T_le hτ.1), Subgroup.le_normalizer hτ.2⟩
  exact normalizer_le_normalizer_oTwoUpper _ h1


theorem FE153_le_V (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (gl : GoldLine153 T V₁ E s) : FE153 E s ≤ VZ T M :=
  conjSubgroup_le_of_mem c.hyp.le_normalizer (c.hyp.T_le gl.s_mem.1) L.le_V

omit [Finite G] in
theorem card_FE153 (L : LineData153 T M V₁ V₂ E) : Nat.card (FE153 E s) = 4 :=
  (E3.card_conjSubgroup E s).trans L.card_eq

omit [Finite G] in
theorem FE153_ne_E (gl : GoldLine153 T V₁ E s) : FE153 E s ≠ E := by
  intro h
  apply gl.s_not_mem
  refine ⟨gl.s_mem.1, ?_⟩
  show s ∈ Subgroup.normalizer (E : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := SetLike.ext_iff.mp h x
  rw [mem_conjSubgroup_iff] at h1
  exact h1.symm


theorem false_of_nonsolvable (c : Ctx153 G T Mc M V₁ V₂ t) (r45 : Res15345 T Mc M V₁ V₂)
    (r49 : Res15349 T Mc M V₁) (r67 : Res15367 T Mc M V₁ V₂ E)
    (hns : ¬ Group.IsSolvable ↥(thompsonJ (G0_153 T Mc M E s) ⊓
      Subgroup.normalizer (V₁ : Set G))) : False := by
  apply hns
  have hle : thompsonJ (G0_153 T Mc M E s) ⊓ Subgroup.normalizer (V₁ : Set G) ≤ M :=
    inf_le_right.trans r45.normalizer₁
  have := isSolvable_M153 c r49.case_one r67.M_eq
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)


end Geometry

end CFSG.Quasithin
