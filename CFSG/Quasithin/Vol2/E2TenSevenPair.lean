module

public import CFSG.Quasithin.Vol2.E2TenSevenCore
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

open scoped commutatorElement

namespace Pair

variable {G : Type} [Group G] {X T M V : Subgroup G} {g : G}

theorem P_le_X [Finite G] (h : Pair X T M V g) :
    (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) ≤ X :=
  h.P_le_pCoreOf.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X)

theorem normal_P [Finite G] (h : Pair X T M V g) :
    (((kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V)).subgroupOf X).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.P_le_X).2 h.le_normalizer_P

theorem normal_J (h : Pair X T M V g) : ((kerIn M X).subgroupOf X).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (kerIn_le.trans h.le_X)).2
    (le_normalizer_kerIn M X)

theorem P_le_J [Finite G] (h : Pair X T M V g) :
    (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) ≤ kerIn M X :=
  h.P_le_pCoreOf.trans h.pCoreOf_le_kerIn

abbrev PP (M V X : Subgroup G) (g : G) : Subgroup G := (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V)

abbrev Jbar (M V X : Subgroup G) (g : G) [((PP M V X g).subgroupOf X).Normal] :
    Subgroup (X ⧸ (PP M V X g).subgroupOf X) :=
  ((kerIn M X).subgroupOf X).map (QuotientGroup.mk' _)

theorem Jbar_le_center [Finite G] (h : Pair X T M V g) [((PP M V X g).subgroupOf X).Normal] :
    Jbar M V X g ≤ Subgroup.center (X ⧸ (PP M V X g).subgroupOf X) := by
  rintro _ ⟨j, hj, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
  change j ∈ (kerIn M X).subgroupOf X at hj
  rw [Subgroup.mem_subgroupOf] at hj
  have hc := h.commutator_kerIn_mem_P x.2 hj
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have key : ((x : G) * j)⁻¹ * (j * x) =
      ((x : G) * j)⁻¹ * ((x : G) * j * (x : G)⁻¹ * (j : G)⁻¹)⁻¹ * (((x : G) * j)⁻¹)⁻¹ := by
    group
  rw [key]
  exact (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_P (X.inv_mem (X.mul_mem x.2
    (kerIn_le.trans h.le_X hj)))) _).mp ((PP M V X g).inv_mem hc)

theorem normal_Jbar (h : Pair X T M V g) [((PP M V X g).subgroupOf X).Normal] :
    (Jbar M V X g).Normal :=
  have := h.normal_J
  Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

noncomputable def quotJbarEquiv [Finite G] (h : Pair X T M V g)
    [((PP M V X g).subgroupOf X).Normal] [(Jbar M V X g).Normal] :
    (X ⧸ (PP M V X g).subgroupOf X) ⧸ Jbar M V X g ≃* StarQuot M X :=
  have := h.normal_J
  QuotientGroup.quotientQuotientEquivQuotient _ _ (Subgroup.subgroupOf_mono X h.P_le_J)

abbrev Vbar (M V X : Subgroup G) (g : G) [((PP M V X g).subgroupOf X).Normal] :
    Subgroup (X ⧸ (PP M V X g).subgroupOf X) :=
  (V.subgroupOf X).map (QuotientGroup.mk' _)

theorem top_eq_commutator_sup_Vbar [Finite G] (h : Pair X T M V g)
    [((PP M V X g).subgroupOf X).Normal] :
    (⊤ : Subgroup (X ⧸ (PP M V X g).subgroupOf X)) =
      commutator (X ⧸ (PP M V X g).subgroupOf X) ⊔ Vbar M V X g := by
  apply le_antisymm _ le_top
  have htop : V.subgroupOf X ⊔ (conjSub g V).subgroupOf X = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h.V_le h.conj_le, ← h.gen, Subgroup.subgroupOf_self]
  rw [← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), ← htop,
    Subgroup.map_sup, sup_le_iff]
  refine ⟨le_sup_right, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  change w ∈ (conjSub g V).subgroupOf X at hw
  rw [Subgroup.mem_subgroupOf, mem_conjSub] at hw
  have huX : g⁻¹ * (w : G) * g ∈ X := X.mul_mem (X.mul_mem (X.inv_mem h.mem) w.2) h.mem
  set u : X := ⟨g⁻¹ * (w : G) * g, huX⟩ with hu
  set γ : X := ⟨g, h.mem⟩ with hγ
  have hwu : w = γ * u * γ⁻¹ := by
    ext; simp only [hu, hγ, Subgroup.coe_mul, Subgroup.coe_inv]; group
  have e : QuotientGroup.mk' ((PP M V X g).subgroupOf X) w =
      ⁅QuotientGroup.mk' ((PP M V X g).subgroupOf X) γ,
        QuotientGroup.mk' ((PP M V X g).subgroupOf X) u⁆ *
        QuotientGroup.mk' ((PP M V X g).subgroupOf X) u := by
    rw [hwu, commutatorElement_def]; simp only [map_mul, map_inv]; group
  rw [e]
  refine Subgroup.mul_mem_sup (Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
    (Subgroup.mem_top _)) ⟨u, ?_, rfl⟩
  change u ∈ V.subgroupOf X
  rw [Subgroup.mem_subgroupOf]
  exact hw

theorem top_eq_Vbar_sup_conj [Finite G] (h : Pair X T M V g)
    [((PP M V X g).subgroupOf X).Normal] :
    (⊤ : Subgroup (X ⧸ (PP M V X g).subgroupOf X)) = Vbar M V X g ⊔
      (Vbar M V X g).map (MulAut.conj (QuotientGroup.mk' ((PP M V X g).subgroupOf X)
        (⟨g, h.mem⟩ : X))).toMonoidHom := by
  apply le_antisymm _ le_top
  have htop : V.subgroupOf X ⊔ (conjSub g V).subgroupOf X = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h.V_le h.conj_le, ← h.gen, Subgroup.subgroupOf_self]
  rw [← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), ← htop,
    Subgroup.map_sup]
  refine sup_le_sup le_rfl ?_
  rintro _ ⟨w, hw, rfl⟩
  change w ∈ (conjSub g V).subgroupOf X at hw
  rw [Subgroup.mem_subgroupOf, mem_conjSub] at hw
  have huX : g⁻¹ * (w : G) * g ∈ X := X.mul_mem (X.mul_mem (X.inv_mem h.mem) w.2) h.mem
  refine ⟨QuotientGroup.mk' _ ⟨g⁻¹ * (w : G) * g, huX⟩, ⟨⟨g⁻¹ * (w : G) * g, huX⟩, hw, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [← map_mul, ← map_inv, ← map_mul]
  congr 1
  ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem commutator_eq_top_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : commutator B = ⊤) : commutator A = ⊤ := by
  have hmap : (commutator B).map e.symm.toMonoidHom = commutator A := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.symm.surjective]
  rw [← hmap, h, Subgroup.map_top_of_surjective _ e.symm.surjective]

theorem Vbar_sq [Finite G] (h : Pair X T M V g) [((PP M V X g).subgroupOf X).Normal] :
    ∀ v ∈ Vbar M V X g, v * v = 1 := by
  rintro _ ⟨u, hu, rfl⟩
  change u ∈ V.subgroupOf X at hu
  rw [Subgroup.mem_subgroupOf] at hu
  rw [← map_mul]
  have : u * u = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]; exact h.elem.2 _ hu)
  rw [this, map_one]

theorem center_quot_facts [Finite G] (h : Pair X T M V g)
    [((PP M V X g).subgroupOf X).Normal]
    (hXs : IsSimpleGroup (StarQuot M X)) (hXp : commutator (StarQuot M X) = ⊤)
    (hXna : ∃ a b : StarQuot M X, a * b ≠ b * a)
    (hlift : ∀ l ∈ commutator (X ⧸ (PP M V X g).subgroupOf X),
      l * l ∈ (Subgroup.center (commutator (X ⧸ (PP M V X g).subgroupOf X))).map
        (commutator (X ⧸ (PP M V X g).subgroupOf X)).subtype → l * l = 1) :
    Subgroup.center (X ⧸ (PP M V X g).subgroupOf X) = Jbar M V X g ∧
      (∀ z ∈ Subgroup.center (X ⧸ (PP M V X g).subgroupOf X), z * z = 1) ∧
      pCoreOf 2 X = kerIn M X := by
  have := h.normal_Jbar
  set e := h.quotJbarEquiv
  have hS : commutator ((X ⧸ (PP M V X g).subgroupOf X) ⧸ Jbar M V X g) = ⊤ :=
    commutator_eq_top_of_mulEquiv e hXp
  have hsimp : IsSimpleGroup ((X ⧸ (PP M V X g).subgroupOf X) ⧸ Jbar M V X g) :=
    MulEquiv.isSimpleGroup e
  have hna : ∃ a b : (X ⧸ (PP M V X g).subgroupOf X) ⧸ Jbar M V X g, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hXna
    exact ⟨e.symm a, e.symm b, fun hh => hab (by simpa using congrArg e hh)⟩
  have hJc := h.Jbar_le_center
  have hZ : Subgroup.center (X ⧸ (PP M V X g).subgroupOf X) = Jbar M V X g :=
    le_antisymm (center_le_of_simple _ hna hsimp) hJc
  have hsq : ∀ z ∈ Subgroup.center (X ⧸ (PP M V X g).subgroupOf X), z * z = 1 :=
    fun z hz => sq_eq_one_of_mem_center _ hJc hS hsimp hna h.Vbar_sq
      h.top_eq_commutator_sup_Vbar hlift hz
  refine ⟨hZ, hsq, le_antisymm h.pCoreOf_le_kerIn ?_⟩
  have hP2 : IsPGroup 2 (PP M V X g) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le h.P_le_pCoreOf
  have hJ2 : IsPGroup 2 (kerIn M X) := by
    intro j
    have hjX : (j : G) ∈ X := kerIn_le.trans h.le_X j.2
    have hjc : QuotientGroup.mk' ((PP M V X g).subgroupOf X) (⟨j, hjX⟩ : X) ∈
        Subgroup.center (X ⧸ (PP M V X g).subgroupOf X) := by
      rw [hZ]
      exact ⟨⟨j, hjX⟩, Subgroup.mem_subgroupOf.2 j.2, rfl⟩
    have hjj := hsq _ hjc
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hjj
    obtain ⟨k, hk⟩ := hP2 ⟨_, hjj⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' := congrArg Subtype.val hk
    simp only [SubmonoidClass.coe_pow, Subgroup.coe_mul, OneMemClass.coe_one] at hk'
    rw [SubmonoidClass.coe_pow, pow_succ', pow_mul, pow_two, OneMemClass.coe_one]
    exact hk'
  exact h.le_pCoreOf_of_le_kerIn hJ2 le_rfl


abbrev Xbar (M V X : Subgroup G) (g : G) : Type := ↥X ⧸ (PP M V X g).subgroupOf X

abbrev piX (M V X : Subgroup G) (g : G) [((PP M V X g).subgroupOf X).Normal] :
    ↥X →* Xbar M V X g :=
  QuotientGroup.mk' ((PP M V X g).subgroupOf X)


section Pre

variable [((PP M V X g).subgroupOf X).Normal]


theorem piX_eq_one_iff {x : G} (hx : x ∈ X) : piX M V X g ⟨x, hx⟩ = 1 ↔ x ∈ PP M V X g := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]


end Pre


theorem exists_two_Vbar [Finite G] (h : Pair X T M V g) [((PP M V X g).subgroupOf X).Normal]
    [(Jbar M V X g).Normal] (hsimp : IsSimpleGroup (Xbar M V X g ⧸ Jbar M V X g))
    (hna : ∃ a b : Xbar M V X g ⧸ Jbar M V X g, a * b ≠ b * a) :
    ∃ v₁ ∈ Vbar M V X g, ∃ v₂ ∈ Vbar M V X g, QuotientGroup.mk' (Jbar M V X g) v₁ ≠ 1 ∧
      QuotientGroup.mk' (Jbar M V X g) v₂ ≠ 1 ∧
      QuotientGroup.mk' (Jbar M V X g) v₁ ≠ QuotientGroup.mk' (Jbar M V X g) v₂ := by
  set q := QuotientGroup.mk' (Jbar M V X g)
  set γ : Xbar M V X g := QuotientGroup.mk' ((PP M V X g).subgroupOf X) (⟨g, h.mem⟩ : X)
  set A := (Vbar M V X g).map q with hA
  have hA2 : ∀ a ∈ A, a * a = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_mul, h.Vbar_sq v hv, map_one]
  have hgen : A ⊔ A.map (MulAut.conj (q γ)).toMonoidHom = ⊤ := by
    have h1 := congrArg (Subgroup.map q) h.top_eq_Vbar_sup_conj
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), Subgroup.map_sup] at h1
    have hf : (MulAut.conj (q γ)).toMonoidHom.comp q = q.comp (MulAut.conj γ).toMonoidHom :=
      MonoidHom.ext fun x => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
          map_inv]
    have key : ∀ K : Subgroup (Xbar M V X g), (K.map q).map (MulAut.conj (q γ)).toMonoidHom =
        (K.map (MulAut.conj γ).toMonoidHom).map q := by
      intro K
      rw [Subgroup.map_map, Subgroup.map_map, hf]
    rw [h1, hA, key]
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := exists_two_of_simple hsimp hna hA2 (q γ) hgen
  obtain ⟨v₁, hv₁, rfl⟩ := ha
  obtain ⟨v₂, hv₂, rfl⟩ := hb
  exact ⟨v₁, hv₁, v₂, hv₂, ha1, hb1, hab⟩

end Pair

end E2

end CFSG.Quasithin
