module

public import CFSG.Sporadic.HNSchreier.Involution
public import CFSG.Sporadic.HNSchreier.Simple
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HN.Local
open CFSG.ComponentClassification.OuterAutomorphisms Matrix Equiv

theorem not_isMulCommutative_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : ¬ IsMulCommutative G := fun hc =>
  h ((@Group.is_simple_iff_prime_card G _ hc).1 inferInstance)

theorem center_eq_bot_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : Subgroup.center G = ⊥ :=
  (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G)).resolve_right fun ht =>
    not_isMulCommutative_of_simple h (Subgroup.center_eq_top_iff.1 ht)

theorem commutator_eq_top_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : commutator G = ⊤ :=
  (IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G)).resolve_left fun hb =>
    not_isMulCommutative_of_simple h ((commutator_eq_bot_iff G).1 hb)

instance jh_simple :
    IsSimpleGroup JH := by
  have := ph_simple
  exact MulEquiv.isSimpleGroup jEquivP

theorem card_JH_not_prime :
    ¬ (Nat.card JH).Prime := by
  rw [card_JH]
  norm_num

theorem center_JH :

    Subgroup.center JH = ⊥ := center_eq_bot_of_simple card_JH_not_prime

theorem orbit_sizes_one : ∀ j : Fin 12, Data.subgroupOrbitSizes[j.val]! = 1 → j = 0 := by
  decide

theorem HP_fixed_unique
    {y : X} (hy : ∀ h ∈ HP, h y = y) : y = x0 := by
  have horb : MulAction.orbit HP y = {y} := by
    ext z
    rw [Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨h, hh⟩, rfl⟩
      exact hy h hh
    · rintro rfl
      exact MulAction.mem_orbit_self z
  have h1 := mem_orbit_hLab y
  have heq : MulAction.orbit HP y = MulAction.orbit HP (repX (hLab y)) :=
    MulAction.orbit_eq_iff.2 h1
  have hcard := card_orbit (hLab y)
  rw [← heq, horb, Nat.card_unique] at hcard
  have h0 := orbit_sizes_one (hLab y) hcard.symm
  rw [h0] at h1
  obtain ⟨⟨h, hh⟩, he⟩ := h1
  rw [← he]
  exact HP_fix_zero hh

theorem mem_HJ_of_normalizes
    {g : JH} (hg : ∀ h ∈ HJ, g * h * g⁻¹ ∈ HJ) : g ∈ HJ := by
  have hfix : ∀ h ∈ HP, h (g⁻¹ • x0) = g⁻¹ • x0 := by
    intro h hh
    rw [← HJ_map] at hh
    obtain ⟨k, hk, rfl⟩ := hh
    have hk' := (mem_HJ_iff_fix _).1 (hg k hk)
    show k • (g⁻¹ • x0) = g⁻¹ • x0
    rw [← mul_smul, show k * g⁻¹ = g⁻¹ * (g * k * g⁻¹) by group, mul_smul, hk']
  have := HP_fixed_unique hfix
  have hginv : g⁻¹ ∈ HJ := (mem_HJ_iff_fix _).2 this
  simpa using inv_mem hginv

theorem false_of_conjCH_eq
    {g : JH} (hgH : g ∈ HJ)
    (hconj : ∀ h : HJ, conjCH h = ⟨g, hgH⟩ * h * (⟨g, hgH⟩ : HJ)⁻¹) : False := by
  set π : Perm (Fin 12) := (thetaJ ⟨g, hgH⟩ : Perm (Fin 12))⁻¹ * swap 0 1
  have hcomm : ∀ σ ∈ alternatingGroup (Fin 12), π * σ = σ * π := by
    intro σ hσ
    obtain ⟨h, hh⟩ := thetaJ.surjective ⟨σ, hσ⟩
    have e := thetaJ_conjCH h
    rw [hconj, map_mul, map_mul, map_inv] at e
    have e' : (thetaJ h : Perm (Fin 12)) = σ := congrArg Subtype.val hh
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e
    rw [e'] at e
    have hs : swap (0 : Fin 12) 1 * swap 0 1 = 1 := Equiv.swap_mul_self 0 1
    have e2 : swap 0 1 * σ = (thetaJ ⟨g, hgH⟩ : Perm (Fin 12)) * σ *
        (thetaJ ⟨g, hgH⟩ : Perm (Fin 12))⁻¹ * swap 0 1 := by
      rw [e, mul_assoc (swap 0 1 * σ) (swap 0 1) (swap 0 1), hs, mul_one]
    show (thetaJ ⟨g, hgH⟩ : Perm (Fin 12))⁻¹ * swap 0 1 * σ =
      σ * ((thetaJ ⟨g, hgH⟩ : Perm (Fin 12))⁻¹ * swap 0 1)
    rw [mul_assoc, e2]
    group
  have hπ := eq_one_of_commute_alt hcomm
  apply tau_not_mem
  have : swap (0 : Fin 12) 1 = (thetaJ ⟨g, hgH⟩ : Perm (Fin 12)) := by
    have := congrArg (fun x => (thetaJ ⟨g, hgH⟩ : Perm (Fin 12)) * x) hπ
    simp only [π, mul_one] at this
    rw [← this, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [this]
  exact (thetaJ ⟨g, hgH⟩).2

theorem conjC_not_inner
    (g : JH) : conjC ≠ MulAut.conj g := by
  intro he
  have hc : ∀ h : JH, conjC h = g * h * g⁻¹ := fun h => by
    rw [he]
    rfl
  have hgH : g ∈ HJ := mem_HJ_of_normalizes fun h hh => by
    rw [← hc]
    exact conjC_mem_HJ hh
  exact false_of_conjCH_eq hgH fun h => Subtype.ext (hc h)

theorem conjC_not_mem_inner :
    conjC ∉ inner JH := by
  rintro ⟨g, hg⟩
  exact conjC_not_inner g hg.symm

theorem conjC_sq :
    conjC * conjC = 1 := MulEquiv.ext conjC_conjC

theorem conjC_ne_one :
    conjC ≠ 1 := fun h => conjC_not_inner 1 (h.trans (map_one _).symm)

theorem orderOf_conjC :
    orderOf conjC = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact conjC_sq) conjC_ne_one

@[expose] def RH :
    Subgroup (GL (Fin hnsData.d) (ZMod 5)) :=
  Subgroup.closure (insert cU (JH : Set (GL (Fin hnsData.d) (ZMod 5))))

theorem JH_le_RH :
    JH ≤ RH := fun _ h => Subgroup.subset_closure (Set.mem_insert_of_mem _ h)

theorem cU_mem_RH :
    cU ∈ RH := Subgroup.subset_closure (Set.mem_insert _ _)

theorem cU_not_mem :
    cU ∉ JH := fun h => matCx_not_range ⟨cU, h⟩ rfl

theorem conj_cU_mem
    {g : GL (Fin hnsData.d) (ZMod 5)} (hg : g ∈ JH) : cU * g * cU ∈ JH := by
  have := cU_conj_mem ⟨g, hg⟩
  rwa [cU_inv] at this

@[expose] def JcH :
    Subgroup (GL (Fin hnsData.d) (ZMod 5)) where
  carrier := {r | r ∈ JH ∨ ∃ g ∈ JH, r = g * cU}
  one_mem' := Or.inl (one_mem _)
  mul_mem' := by
    rintro x y (hx | ⟨g, hg, rfl⟩) (hy | ⟨h, hh, rfl⟩)
    · exact Or.inl (mul_mem hx hy)
    · exact Or.inr ⟨x * h, mul_mem hx hh, by group⟩
    · refine Or.inr ⟨g * (cU * y * cU), mul_mem hg (conj_cU_mem hy), ?_⟩
      rw [show g * (cU * y * cU) * cU = g * cU * y * (cU * cU) by group, cU_mul_self, mul_one]
    · refine Or.inl ?_
      have e : g * cU * (h * cU) = g * (cU * h * cU) := by group
      rw [e]
      exact mul_mem hg (conj_cU_mem hh)
  inv_mem' := by
    rintro x (hx | ⟨g, hg, rfl⟩)
    · exact Or.inl (inv_mem hx)
    · refine Or.inr ⟨cU * g⁻¹ * cU, conj_cU_mem (inv_mem hg), ?_⟩
      rw [_root_.mul_inv_rev, cU_inv, mul_assoc (cU * g⁻¹) cU cU, cU_mul_self, mul_one]

theorem mem_RH_iff
    (r : GL (Fin hnsData.d) (ZMod 5)) : r ∈ RH ↔ r ∈ JH ∨ ∃ g ∈ JH, r = g * cU := by
  constructor
  · intro hr
    have hle : RH ≤ JcH := by
      rw [RH, Subgroup.closure_le]
      rintro x (rfl | hx)
      · exact Or.inr ⟨1, one_mem _, (one_mul _).symm⟩
      · exact Or.inl hx
    exact hle hr
  · rintro (h | ⟨g, hg, rfl⟩)
    · exact JH_le_RH h
    · exact mul_mem (JH_le_RH hg) cU_mem_RH

theorem JH_normal_RH
    {r : GL (Fin hnsData.d) (ZMod 5)} (hr : r ∈ RH)
    {g : GL (Fin hnsData.d) (ZMod 5)} (hg : g ∈ JH) : r * g * r⁻¹ ∈ JH := by
  rcases (mem_RH_iff r).1 hr with hr | ⟨k, hk, rfl⟩
  · exact mul_mem (mul_mem hr hg) (inv_mem hr)
  · have e : k * cU * g * (k * cU)⁻¹ = k * (cU * g * cU⁻¹) * k⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hk (cU_conj_mem ⟨g, hg⟩)) (inv_mem hk)


theorem index_JH_RH :
    (JH.subgroupOf RH).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨cU, cU_mem_RH⟩, fun b => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  rcases (mem_RH_iff b).1 b.2 with hb | ⟨g, hg, he⟩
  · refine Or.inr ⟨hb, fun h => cU_not_mem ?_⟩
    have := mul_mem (inv_mem hb) h
    rwa [inv_mul_cancel_left] at this
  · refine Or.inl ⟨?_, fun h => cU_not_mem ?_⟩
    · show (b : GL (Fin hnsData.d) (ZMod 5)) * cU ∈ JH
      rw [he, mul_assoc, cU_mul_self, mul_one]
      exact hg
    · have := mul_mem (inv_mem hg) h
      rwa [he, inv_mul_cancel_left] at this

theorem card_RH :
    Nat.card RH = 546061824000000 := by
  rw [← Subgroup.card_mul_index (JH.subgroupOf RH), index_JH_RH,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe JH_le_RH).toEquiv, card_JH]


theorem eq_one_of_centralizes
    {r : GL (Fin hnsData.d) (ZMod 5)} (hr : r ∈ RH)
    (hc : ∀ g ∈ JH, r * g = g * r) : r = 1 := by
  rcases (mem_RH_iff r).1 hr with hr' | ⟨k, hk, rfl⟩
  · have : (⟨r, hr'⟩ : JH) ∈ Subgroup.center JH := Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (hc g g.2).symm
    rw [center_JH, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · exfalso
    apply conjC_not_inner ⟨k, hk⟩⁻¹
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    show cU * (g : GL (Fin hnsData.d) (ZMod 5)) * cU⁻¹ = k⁻¹ * g * k⁻¹⁻¹
    have e := hc g g.2
    rw [inv_inv]
    calc cU * (g : GL (Fin hnsData.d) (ZMod 5)) * cU⁻¹
        = k⁻¹ * (k * cU * g) * cU⁻¹ := by group
      _ = k⁻¹ * (g * (k * cU)) * cU⁻¹ := by rw [e]
      _ = k⁻¹ * g * k := by group


@[expose] def conjRAut
    (r : GL (Fin hnsData.d) (ZMod 5)) (hr : r ∈ RH) : MulAut JH where
  toFun g := ⟨r * g * r⁻¹, JH_normal_RH hr g.2⟩
  invFun g := ⟨r⁻¹ * g * r, by simpa using JH_normal_RH (inv_mem hr) g.2⟩
  left_inv g := Subtype.ext (by
    show r⁻¹ * (r * (g : GL (Fin hnsData.d) (ZMod 5)) * r⁻¹) * r = g
    group)
  right_inv g := Subtype.ext (by
    show r * (r⁻¹ * (g : GL (Fin hnsData.d) (ZMod 5)) * r) * r⁻¹ = g
    group)
  map_mul' g h := Subtype.ext (by
    show r * ((g : GL (Fin hnsData.d) (ZMod 5)) * h) * r⁻¹ = r * g * r⁻¹ * (r * h * r⁻¹)
    group)

@[expose] def conjR :
    RH →* MulAut JH where
  toFun r := conjRAut r r.2
  map_one' := MulEquiv.ext fun g => Subtype.ext (by
    show (1 : GL (Fin hnsData.d) (ZMod 5)) * g * 1⁻¹ = g
    group)
  map_mul' r s := MulEquiv.ext fun g => Subtype.ext (by
    show (r : GL (Fin hnsData.d) (ZMod 5)) * s * g * ((r : GL (Fin hnsData.d) (ZMod 5)) * s)⁻¹ =
      r * (s * g * (s : GL (Fin hnsData.d) (ZMod 5))⁻¹) * (r : GL (Fin hnsData.d) (ZMod 5))⁻¹
    group)

theorem conjR_apply
    (r : RH) (g : JH) :
    ((conjR r g : JH) : GL (Fin hnsData.d) (ZMod 5)) =
      (r : GL (Fin hnsData.d) (ZMod 5)) * g * (r : GL (Fin hnsData.d) (ZMod 5))⁻¹ := rfl

theorem conjR_JH
    (g : JH) : conjR ⟨g, JH_le_RH g.2⟩ = MulAut.conj g :=
  MulEquiv.ext fun _ => Subtype.ext rfl

theorem conjR_cU :
    conjR ⟨cU, cU_mem_RH⟩ = conjC := MulEquiv.ext fun _ => Subtype.ext rfl

theorem conjR_injective :
    Function.Injective conjR := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro r hr
  rw [MonoidHom.mem_ker] at hr
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  refine eq_one_of_centralizes r.2 fun g hg => ?_
  have := congrArg (fun φ : MulAut JH => ((φ ⟨g, hg⟩ : JH) : GL (Fin hnsData.d) (ZMod 5))) hr
  simp only [conjR_apply, MulAut.one_apply] at this
  calc (r : GL (Fin hnsData.d) (ZMod 5)) * g =
      (r : GL (Fin hnsData.d) (ZMod 5)) * g * (r : GL (Fin hnsData.d) (ZMod 5))⁻¹ * r := by group
    _ = g * r := by rw [this]


@[expose] def hnAutCongr :
    MulAut JH ≃* MulAut Blueprint.NativeSporadic.HN :=
  @MulAut.congr JH _ Blueprint.NativeSporadic.HN Units.instGroup hnEquivJ.symm

@[expose] def hnOuterEquiv :
    Outer JH ≃* Outer Blueprint.NativeSporadic.HN :=
  @equivalence JH Blueprint.NativeSporadic.HN _ Units.instGroup hnEquivJ.symm

@[expose] def hnOuterC :
    MulAut Blueprint.NativeSporadic.HN := hnAutCongr conjC

theorem orderOf_outer_conjC :
    orderOf (QuotientGroup.mk conjC : Outer JH) = 2 := by
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow, pow_two, conjC_sq, QuotientGroup.mk_one]
  · intro h
    rw [QuotientGroup.eq_one_iff] at h
    exact conjC_not_mem_inner h

theorem hnOuterEquiv_mk (φ : MulAut JH) :
    hnOuterEquiv (QuotientGroup.mk φ) = QuotientGroup.mk (hnAutCongr φ) := rfl


end CFSG.Sporadic.HNSchreier
