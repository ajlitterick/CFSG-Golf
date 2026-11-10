module

public import CFSG.Monster.B.CTIB.UniqueComponent
public import CFSG.Monster.B.TwoA.Amalgam.NativeChainFinal
public import CFSG.Monster.B.CTIB.Rep4371Main

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.B.CTIB

theorem mem_centralizer_singleton_self {G : Type*} [Group G] (a : G) :
    a ∈ Subgroup.centralizer {a} :=
  Subgroup.mem_centralizer_singleton_iff.2 rfl

theorem mem_center_iff_of_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K) {y : H} :
    y ∈ Subgroup.center H ↔ e y ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h z
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [← map_mul, ← map_mul, h w]
  · intro h w
    apply e.injective
    rw [map_mul, map_mul, h]

@[expose] def cV0 : vStab cv0 :=
  ⟨clabelS cv0, mem_vStab_cv0.2 (by rw [coe_clabelS, clabel_cv0]; exact cQ_mem_Eam)⟩

theorem coe_cV0 :
    (cV0 : Shat) = clabelS cv0 := rfl

theorem orderOf_cV0 :
    orderOf cV0 = 2 := by
  rw [← Subgroup.orderOf_coe, coe_cV0, orderOf_clabelS]

theorem vStab_cv0_eq :
    vStab cv0 = Eam.subgroupOf Shat := by
  ext s
  rw [mem_vStab_cv0, Subgroup.mem_subgroupOf]

@[expose] def vStabEam :
    vStab cv0 ≃* Eam :=
  (MulEquiv.subgroupCongr vStab_cv0_eq).trans (Subgroup.subgroupOfEquivOfLe Eam_le_Shat)

theorem coe_vStabEam
    (y : vStab cv0) : ((vStabEam y : Eam) : Dfull) = ((y : Shat) : Dfull) :=
  rfl

theorem vStabEam_cV0 :
    vStabEam cV0 = cE' :=
  Subtype.ext (by rw [coe_vStabEam, coe_cV0, coe_clabelS, clabel_cv0]; rfl)

theorem center_vStab_cv0 :
    Subgroup.center (vStab cv0) = Subgroup.zpowers cV0 := by
  ext y
  rw [mem_center_iff_of_mulEquiv vStabEam, derivedCoverInput_holds.2.2.1,
    Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, vStabEam.injective (by rw [map_zpow, vStabEam_cV0, hk])⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [map_zpow, vStabEam_cV0]⟩

theorem eq_one_or_eq_cV0
    {y : vStab cv0} (hy : y ∈ Subgroup.zpowers cV0) : y = 1 ∨ y = cV0 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← zpow_mod_orderOf, orderOf_cV0]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

theorem centralizer_equiv_self_eq_cV0
    {G : Type*} [Group G] {a : G} (ha : a ≠ 1)
    (Ψ : Subgroup.centralizer {a} ≃* vStab cv0) :
    Ψ ⟨a, mem_centralizer_singleton_self a⟩ = cV0 := by
  have hcen : Ψ ⟨a, mem_centralizer_singleton_self a⟩ ∈ Subgroup.center (vStab cv0) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨x, rfl⟩ := Ψ.surjective w
    rw [← map_mul, ← map_mul]
    exact congrArg Ψ (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 x.2))
  rw [center_vStab_cv0] at hcen
  rcases eq_one_or_eq_cV0 hcen with h | h
  · exact absurd (congrArg Subtype.val (Ψ.injective (h.trans (map_one Ψ).symm))) ha
  · exact h

theorem nonempty_centralizer_equiv_vStab
    {d₀ : NativeSporadic.B} (hd₀ : orderOf d₀ = 2)
    (hrank : Matrix.rank (d₀.val.val - 1) = 1860) :
    Nonempty (Subgroup.centralizer {d₀} ≃* vStab cv0) := by
  have hs : orderOf (iotaEquiv d₀) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hd₀
  have hr := rank_iotaEquiv_symm (iotaEquiv d₀)
  rw [MulEquiv.symm_apply_apply, hrank] at hr
  have hc : IsConj (sEquiv (iotaEquiv d₀)) (sEquiv labelS) :=
    sEquiv.toMonoidHom.map_isConj (isConj_labelS_of_rank hs hr.symm)
  have hcS : cS⁻¹ = cS := Subtype.ext (inv_eq_of_mul_eq_one_left Sp8.cQ_mul_self)
  rw [sEquiv_labelS, hcS] at hc
  obtain ⟨g, hg⟩ := isConj_iff.1 hc
  have Ψ₁ : Subgroup.centralizer {d₀} ≃* Subgroup.centralizer {iotaEquiv d₀} := by
    with_reducible_and_instances exact centralizerEquiv iotaEquiv d₀
  have e : Subgroup.centralizer {(MulAut.conj g) (sEquiv (iotaEquiv d₀))} = vStab cv0 := by
    rw [MulAut.conj_apply, hg,
      centralizer_cS native_global_label_bijection_and_full_vertex_centralizer.2.2.2.1,
      vStab_cv0_eq]
  exact ⟨Ψ₁.trans ((centralizerEquiv sEquiv (iotaEquiv d₀)).trans
    ((centralizerEquiv (MulAut.conj g) _).trans (MulEquiv.subgroupCongr e)))⟩

@[expose] def centralizerVStabEquiv
    {d₀ : NativeSporadic.B} (hd₀ : orderOf d₀ = 2)
    (hrank : Matrix.rank (d₀.val.val - 1) = 1860) :
    Subgroup.centralizer {d₀} ≃* vStab cv0 :=
  Classical.choice (nonempty_centralizer_equiv_vStab hd₀ hrank)

variable {G : Type*} [Group G]

@[expose] def psiOf
    {d₀ : NativeSporadic.B} (hd₀ : orderOf d₀ = 2)
    (hrank : Matrix.rank (d₀.val.val - 1) = 1860) {d : G}
    (φ : Subgroup.centralizer {d} ≃* Subgroup.centralizer {d₀}) :
    Subgroup.centralizer {d} ≃* vStab cv0 :=
  φ.trans (centralizerVStabEquiv hd₀ hrank)

theorem psiOf_self
    {d₀ : NativeSporadic.B} (hd₀ : orderOf d₀ = 2)
    (hrank : Matrix.rank (d₀.val.val - 1) = 1860) {d : G} (hd : d ≠ 1)
    (φ : Subgroup.centralizer {d} ≃* Subgroup.centralizer {d₀}) :
    psiOf hd₀ hrank φ ⟨d, mem_centralizer_singleton_self d⟩ = cV0 :=
  centralizer_equiv_self_eq_cV0 hd _

@[expose] def centralizerConjEquiv {d a : G} (g : G) (hg : g * d * g⁻¹ = a) :
    Subgroup.centralizer {a} ≃* Subgroup.centralizer {d} where
  toFun x := ⟨g⁻¹ * x * g, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx : (x : G) * (g * d * g⁻¹) = g * d * g⁻¹ * x := by
      rw [hg]
      exact Subgroup.mem_centralizer_singleton_iff.1 x.2
    calc g⁻¹ * x * g * d = g⁻¹ * (x * (g * d * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * d * g⁻¹ * x) * g := by rw [hx]
      _ = d * (g⁻¹ * x * g) := by group⟩
  invFun y := ⟨g * y * g⁻¹, by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    have hy := Subgroup.mem_centralizer_singleton_iff.1 y.2
    calc g * y * g⁻¹ * (g * d * g⁻¹) = g * (y * d) * g⁻¹ := by group
      _ = g * (d * y) * g⁻¹ := by rw [hy]
      _ = g * d * g⁻¹ * (g * y * g⁻¹) := by group⟩
  left_inv x := Subtype.ext (show g * (g⁻¹ * (x : G) * g) * g⁻¹ = x by group)
  right_inv y := Subtype.ext (show g⁻¹ * (g * (y : G) * g⁻¹) * g = y by group)
  map_mul' x y := Subtype.ext (show g⁻¹ * ((x : G) * y) * g = g⁻¹ * x * g * (g⁻¹ * y * g) by
    group)

theorem coe_centralizerConjEquiv {d a : G} (g : G) (hg : g * d * g⁻¹ = a)
    (x : Subgroup.centralizer {a}) : (centralizerConjEquiv g hg x : G) = g⁻¹ * x * g := rfl

theorem coe_centralizerConjEquiv_symm {d a : G} (g : G) (hg : g * d * g⁻¹ = a)
    (y : Subgroup.centralizer {d}) :
    ((centralizerConjEquiv g hg).symm y : G) = g * y * g⁻¹ := rfl

@[expose] def conjugator {d a : G} (ha : IsConj d a) : G := Classical.choose (isConj_iff.1 ha)

theorem conjugator_spec {d a : G} (ha : IsConj d a) :
    conjugator ha * d * (conjugator ha)⁻¹ = a :=
  Classical.choose_spec (isConj_iff.1 ha)

@[expose] def psiAt
    {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0) {a : G}
    (ha : IsConj d a) : Subgroup.centralizer {a} ≃* vStab cv0 :=
  (centralizerConjEquiv (conjugator ha) (conjugator_spec ha)).trans ψ

theorem psiAt_apply
    {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0) {a : G}
    (ha : IsConj d a) (x : Subgroup.centralizer {a}) :
    psiAt ψ ha x = ψ (centralizerConjEquiv (conjugator ha) (conjugator_spec ha) x) := rfl

theorem psiAt_self
    {d : G} (hd : d ≠ 1) (ψ : Subgroup.centralizer {d} ≃* vStab cv0) {a : G}
    (ha : IsConj d a) : psiAt ψ ha ⟨a, mem_centralizer_singleton_self a⟩ = cV0 := by
  refine centralizer_equiv_self_eq_cV0 (fun h => hd ?_) _
  subst h
  exact isConj_one_left.1 ha

theorem psiAt_eq_conj
    {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0) {a : G}
    (ha : IsConj d a) (g : G) (hg : g * d * g⁻¹ = a) :
    ∃ y : vStab cv0, ∀ x : Subgroup.centralizer {a},
      psiAt ψ ha x = y * ψ (centralizerConjEquiv g hg x) * y⁻¹ := by
  set g₀ := conjugator ha with hg₀
  have h₀ : g₀ * d * g₀⁻¹ = a := conjugator_spec ha
  have hk : g₀⁻¹ * g ∈ Subgroup.centralizer {d} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g₀⁻¹ * g * d = g₀⁻¹ * (g * d * g⁻¹) * g := by group
      _ = g₀⁻¹ * (g₀ * d * g₀⁻¹) * g := by rw [hg, h₀]
      _ = d * (g₀⁻¹ * g) := by group
  refine ⟨ψ ⟨_, hk⟩, fun x => ?_⟩
  rw [psiAt_apply, ← map_inv, ← map_mul, ← map_mul]
  refine congrArg ψ (Subtype.ext ?_)
  show g₀⁻¹ * (x : G) * g₀ = g₀⁻¹ * g * (g⁻¹ * x * g) * (g₀⁻¹ * g)⁻¹
  group

theorem psiAt_conj
    {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0) {a b : G}
    (ha : IsConj d a) (hb : IsConj d b) (h : G) (hab : h * a * h⁻¹ = b) :
    ∃ y : vStab cv0, ∀ x : Subgroup.centralizer {a},
      psiAt ψ hb ((centralizerConjEquiv h hab).symm x) = y * psiAt ψ ha x * y⁻¹ := by
  have h₀ := conjugator_spec ha
  have hg : h * conjugator ha * d * (h * conjugator ha)⁻¹ = b :=
    calc h * conjugator ha * d * (h * conjugator ha)⁻¹ =
        h * (conjugator ha * d * (conjugator ha)⁻¹) * h⁻¹ := by group
      _ = b := by rw [h₀, hab]
  obtain ⟨y, hy⟩ := psiAt_eq_conj ψ hb _ hg
  refine ⟨y, fun x => ?_⟩
  rw [hy, psiAt_apply]
  congr 3
  refine Subtype.ext ?_
  show (h * conjugator ha)⁻¹ * (h * (x : G) * h⁻¹) * (h * conjugator ha) =
    (conjugator ha)⁻¹ * x * conjugator ha
  group

theorem natCard_centralizer_of_equiv
    {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0) :
    Nat.card (Subgroup.centralizer {d}) = 306129918735099415756800 :=
  (Nat.card_congr ψ.toEquiv).trans (natCard_vStab_eq cv0)

theorem natCard_conjugatesOf (d : G) :
    Nat.card (conjugatesOf d) = (Subgroup.centralizer {d}).index := by
  have horb : MulAction.orbit (ConjAct G) d = conjugatesOf d := by
    ext x
    rw [ConjAct.mem_orbit_conjAct]
    exact isConj_comm
  have hstab : (MulAction.stabilizer (ConjAct G) d).comap
      (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom = Subgroup.centralizer {d} := by
    ext g
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, ConjAct.toConjAct_smul]
    constructor
    · intro h
      calc g * d = g * d * g⁻¹ * g := by group
        _ = d * g := by rw [h]
    · intro h
      rw [h, mul_inv_cancel_right]
  rw [← hstab, Subgroup.index_comap_of_surjective _ ConjAct.toConjAct.surjective,
    MulAction.index_stabilizer, horb, Nat.card_coe_set_eq]

abbrev dClass (d : G) : Set G := conjugatesOf d

theorem card_dClass_mul
    {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0) :
    Nat.card (dClass d) * 306129918735099415756800 = Nat.card G := by
  rw [natCard_conjugatesOf, ← natCard_centralizer_of_equiv ψ, mul_comm]
  exact (Subgroup.centralizer {d}).card_mul_index

theorem gside_setup
    (d₀ : NativeSporadic.B) (hd₀ : orderOf d₀ = 2)
    (hrank : Matrix.rank (d₀.val.val - 1) = 1860)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (d : G) (hd : orderOf d = 2)
    (φ : Subgroup.centralizer {d} ≃* Subgroup.centralizer {d₀}) :
    psiOf hd₀ hrank φ ⟨d, mem_centralizer_singleton_self d⟩ = cV0 ∧
    (∀ (a : G) (ha : IsConj d a),
      psiAt (psiOf hd₀ hrank φ) ha ⟨a, mem_centralizer_singleton_self a⟩ = cV0) ∧
    (∀ (a b : G) (ha : IsConj d a) (hb : IsConj d b) (h : G) (hab : h * a * h⁻¹ = b),
      ∃ y : vStab cv0, ∀ x : Subgroup.centralizer {a},
        psiAt (psiOf hd₀ hrank φ) hb ((centralizerConjEquiv h hab).symm x) =
          y * psiAt (psiOf hd₀ hrank φ) ha x * y⁻¹) ∧
    Nat.card (Subgroup.centralizer {d}) = 306129918735099415756800 ∧
    Nat.card (conjugatesOf d) = (Subgroup.centralizer {d}).index := by
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hd
    exact absurd hd (by norm_num)
  exact ⟨psiOf_self hd₀ hrank hd1 φ, fun a ha => psiAt_self hd1 _ ha,
    fun a b ha hb h hab => psiAt_conj _ ha hb h hab,
    natCard_centralizer_of_equiv (psiOf hd₀ hrank φ), natCard_conjugatesOf d⟩

end CFSG.Monster.B.GSide
