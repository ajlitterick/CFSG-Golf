module

public import CFSG.Quasithin.Background.G11Basic
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin

open scoped Pointwise

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

@[expose] def addEquivToLinear {V' : Type*} [AddCommGroup V'] [Module (ZMod 2) V'] (e : V ≃+ V') :
    V ≃ₗ[ZMod 2] V' where
  toFun := e
  map_add' := e.map_add
  map_smul' c v := by
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · simp
    · simp
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv

@[simp] theorem addEquivToLinear_apply {V' : Type*} [AddCommGroup V'] [Module (ZMod 2) V']
    (e : V ≃+ V') (v : V) : addEquivToLinear e v = e v := rfl

@[expose] def linEquivMulAut : (V ≃ₗ[ZMod 2] V) ≃* MulAut (Multiplicative V) where
  toFun g := AddEquiv.toMultiplicative g.toAddEquiv
  invFun f := addEquivToLinear (AddEquiv.toMultiplicative.symm f)
  left_inv g := by
    ext v
    rfl
  right_inv f := by
    ext v
    rfl
  map_mul' g h := by
    ext v
    rfl

@[simp] theorem linEquivMulAut_apply (g : GLV V) (q : Multiplicative V) :
    linEquivMulAut g q = Multiplicative.ofAdd (g (Multiplicative.toAdd q)) := rfl


theorem linEquivMulAut_symm_apply (f : MulAut (Multiplicative V)) (v : V) :
    (linEquivMulAut.symm f) v = Multiplicative.toAdd (f (Multiplicative.ofAdd v)) := rfl


theorem multiplicative_sq_eq_one (q : Multiplicative V) : q ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul (ZMod 2)]
  have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [h2, zero_smul]

instance linMulAct : MulDistribMulAction (GLV V) (Multiplicative V) where
  smul g q := Multiplicative.ofAdd (g (Multiplicative.toAdd q))
  one_smul q := rfl
  mul_smul g h q := rfl
  smul_mul g p q := by
    show Multiplicative.ofAdd (g (Multiplicative.toAdd p + Multiplicative.toAdd q)) = _
    rw [map_add]
    rfl
  smul_one g := by
    show Multiplicative.ofAdd (g 0) = 1
    rw [map_zero]
    rfl

theorem linMulAct_smul (g : GLV V) (q : Multiplicative V) :
    g • q = Multiplicative.ofAdd (g (Multiplicative.toAdd q)) := rfl

@[simp] theorem linMulAct_smul_ofAdd (g : GLV V) (v : V) :
    g • (Multiplicative.ofAdd v) = Multiplicative.ofAdd (g v) := rfl

@[simp] theorem toAdd_linMulAct_smul (g : GLV V) (q : Multiplicative V) :
    Multiplicative.toAdd (g • q) = g (Multiplicative.toAdd q) := rfl


@[expose] def subToSubgroup : Submodule (ZMod 2) V ≃o Subgroup (Multiplicative V) where
  toFun U := AddSubgroup.toSubgroup U.toAddSubgroup
  invFun S :=
    { carrier := {v | Multiplicative.ofAdd v ∈ S}
      add_mem' := fun {a b} ha hb => S.mul_mem ha hb
      zero_mem' := S.one_mem
      smul_mem' := fun c v hv => by
        rcases zmod2_eq_zero_or_one c with rfl | rfl
        · rw [zero_smul]
          exact S.one_mem
        · rw [one_smul]
          exact hv }
  left_inv U := by
    ext v
    rfl
  right_inv S := by
    ext v
    rfl
  map_rel_iff' := by
    intro U U'
    constructor
    · intro h v hv
      exact h hv
    · intro h v hv
      exact h hv

theorem mem_subToSubgroup {U : Submodule (ZMod 2) V} {q : Multiplicative V} :
    q ∈ subToSubgroup U ↔ Multiplicative.toAdd q ∈ U := Iff.rfl


theorem subToSubgroup_inj {U U' : Submodule (ZMod 2) V} :
    subToSubgroup U = subToSubgroup U' ↔ U = U' := subToSubgroup.injective.eq_iff

theorem subToSubgroup_span (S : Set V) :
    subToSubgroup (Submodule.span (ZMod 2) S) = Subgroup.closure (Multiplicative.ofAdd '' S) := by
  apply le_antisymm
  · refine subToSubgroup.le_symm_apply.1 (Submodule.span_le.2 fun s hs => ?_)
    show Multiplicative.ofAdd s ∈ Subgroup.closure (Multiplicative.ofAdd '' S)
    exact Subgroup.subset_closure ⟨s, hs, rfl⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨s, hs, rfl⟩
    show s ∈ Submodule.span (ZMod 2) S
    exact Submodule.subset_span hs

@[expose] def toMulSub (K : Subgroup (GLV V)) : Subgroup (MulAut (Multiplicative V)) :=
  K.map linEquivMulAut.toMonoidHom

theorem mem_toMulSub {K : Subgroup (GLV V)} {f : MulAut (Multiplicative V)} :
    f ∈ toMulSub K ↔ linEquivMulAut.symm f ∈ K := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    simpa using hg
  · intro h
    exact ⟨_, h, by simp⟩

theorem linEquivMulAut_mem_toMulSub {K : Subgroup (GLV V)} {g : GLV V} :
    linEquivMulAut g ∈ toMulSub K ↔ g ∈ K := by
  rw [mem_toMulSub, MulEquiv.symm_apply_apply]

theorem toMulSub_le_iff {K K' : Subgroup (GLV V)} : toMulSub K ≤ toMulSub K' ↔ K ≤ K' :=
  (MulEquiv.mapSubgroup (linEquivMulAut (V := V))).le_iff_le (x := K) (y := K')

theorem toMulSub_injective : Function.Injective (toMulSub (V := V)) := fun _ _ h =>
  le_antisymm (toMulSub_le_iff.1 h.le) (toMulSub_le_iff.1 h.ge)

@[expose] def toMulSubIso : Subgroup (GLV V) ≃o Subgroup (MulAut (Multiplicative V)) :=
  MulEquiv.mapSubgroup linEquivMulAut


theorem toMulSub_sup (K K' : Subgroup (GLV V)) : toMulSub (K ⊔ K') = toMulSub K ⊔ toMulSub K' :=
  toMulSubIso.map_sup K K'


@[expose] def toMulSubEquiv (K : Subgroup (GLV V)) : ↥K ≃* ↥(toMulSub K) :=
  linEquivMulAut.subgroupMap K

@[simp] theorem coe_toMulSubEquiv (K : Subgroup (GLV V)) (k : ↥K) :
    ((toMulSubEquiv K k : ↥(toMulSub K)) : MulAut (Multiplicative V)) =
      linEquivMulAut (k : GLV V) := rfl


end G11

namespace XMod

section Congr

variable {A A' : Type*} [Group A] [Group A'] {Q : Type*} [CommGroup Q]
  [MulDistribMulAction A Q] [MulDistribMulAction A' Q] (e : A ≃* A')
  (he : ∀ (a : A) (q : Q), e a • q = a • q)

include he

theorem isInv_congr_equiv (L : Subgroup Q) : IsInv A' L ↔ IsInv A L := by
  constructor
  · intro h a l hl
    rw [← he a l]
    exact h (e a) l hl
  · intro h a' l hl
    obtain ⟨a, rfl⟩ := e.surjective a'
    rw [he a l]
    exact h a l hl


theorem isIrrSec_congr_equiv (C L : Subgroup Q) : IsIrrSec A' C L ↔ IsIrrSec A C L := by
  unfold IsIrrSec
  simp only [isInv_congr_equiv e he]

theorem isIrr_congr_equiv (L : Subgroup Q) : IsIrr A' L ↔ IsIrr A L := by
  unfold IsIrr
  rw [isInv_congr_equiv e he, isIrrSec_congr_equiv e he]


theorem iso_congr_equiv (L L' : Subgroup Q) : Iso A' L L' ↔ Iso A L L' := by
  unfold Iso
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, fun a l l' h => ?_⟩
    rw [← he a] at h ⊢
    exact hφ (e a) l l' h
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, fun a' l l' h => ?_⟩
    obtain ⟨a, rfl⟩ := e.surjective a'
    rw [he a] at h ⊢
    exact hφ a l l' h


end Congr

end XMod

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[simp] theorem toMulSubEquiv_smul (K : Subgroup (GLV V)) (k : ↥K) (q : Multiplicative V) :
    (toMulSubEquiv K k) • q = k • q := rfl

section XMod

variable {K : Subgroup (GLV V)} {U C L I J M : Submodule (ZMod 2) V}

theorem smul_mul_inv_eq (g : GLV V) (v : V) :
    (g • Multiplicative.ofAdd v) * (Multiplicative.ofAdd v)⁻¹ = Multiplicative.ofAdd (g v - v) := by
  apply Multiplicative.toAdd.injective
  simp [sub_eq_add_neg]

theorem invariant_iff_isInv : Invariant K U ↔ XMod.IsInv ↥K (subToSubgroup U) := by
  constructor
  · intro h a l hl
    exact h a a.2 (Multiplicative.toAdd l) hl
  · intro h k hk u hu
    exact h ⟨k, hk⟩ (Multiplicative.ofAdd u) hu

theorem invariant_symm_iff {S : Subgroup (Multiplicative V)} :
    Invariant K (subToSubgroup.symm S) ↔ XMod.IsInv ↥K S := by
  rw [invariant_iff_isInv, OrderIso.apply_symm_apply]

theorem fixed_eq (U : Submodule (ZMod 2) V) :
    XMod.fixed ↥K (subToSubgroup U) = subToSubgroup (fixedSpace K ⊓ U) := by
  ext q
  constructor
  · rintro ⟨hqU, hfix⟩
    exact ⟨fun k hk => congrArg Multiplicative.toAdd (hfix ⟨k, hk⟩), hqU⟩
  · rintro ⟨hf, hqU⟩
    exact ⟨hqU, fun a => congrArg Multiplicative.ofAdd (hf a a.2)⟩


theorem commOf_eq (U : Submodule (ZMod 2) V) :
    XMod.commOf ↥K (subToSubgroup U) = subToSubgroup (commSpace K U) := by
  rw [commSpace, subToSubgroup_span, XMod.commOf]
  congr 1
  ext c
  constructor
  · rintro ⟨a, l, hl, rfl⟩
    refine ⟨(a : GLV V) (Multiplicative.toAdd l) - Multiplicative.toAdd l,
      ⟨a, a.2, Multiplicative.toAdd l, hl, rfl⟩, ?_⟩
    exact (smul_mul_inv_eq (a : GLV V) (Multiplicative.toAdd l)).symm
  · rintro ⟨_, ⟨k, hk, u, hu, rfl⟩, rfl⟩
    exact ⟨⟨k, hk⟩, Multiplicative.ofAdd u, hu, (smul_mul_inv_eq k u).symm⟩


theorem irrSec_iff : IrrSec K C L ↔ XMod.IsIrrSec ↥K (subToSubgroup C) (subToSubgroup L) := by
  unfold IrrSec XMod.IsIrrSec
  rw [subToSubgroup.lt_iff_lt]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h J' hJ' hCJ' hJ'L
    have h1 := h (subToSubgroup.symm J') (invariant_symm_iff.2 hJ')
      (subToSubgroup.le_symm_apply.2 hCJ') (subToSubgroup.symm_apply_le.2 hJ'L)
    rcases h1 with h1 | h1
    · left
      rw [← subToSubgroup.apply_symm_apply J', h1]
    · right
      rw [← subToSubgroup.apply_symm_apply J', h1]
  · intro h J hJ hCJ hJL
    rcases h (subToSubgroup J) (invariant_iff_isInv.1 hJ) (subToSubgroup.monotone hCJ)
      (subToSubgroup.monotone hJL) with h1 | h1
    · exact Or.inl (subToSubgroup.injective h1)
    · exact Or.inr (subToSubgroup.injective h1)

theorem isIrr_iff : IsIrr K U ↔ XMod.IsIrr ↥K (subToSubgroup U) := by
  unfold IsIrr XMod.IsIrr
  rw [invariant_iff_isInv, irrSec_iff, OrderIso.map_bot]

theorem irrPlus_iff : IrrPlus K I ↔ XMod.IsIrrPlus ↥K (subToSubgroup I) := by
  unfold IrrPlus XMod.IsIrrPlus
  rw [invariant_iff_isInv, irrSec_iff, fixed_eq, commOf_eq, subToSubgroup_inj]

theorem mem_irrPlus_top_iff :
    subToSubgroup I ∈ CFSG.Quasithin.IrrPlus K (⊤ : Subgroup (Multiplicative V)) ↔ IrrPlus K I := by
  rw [irrPlus_iff]
  exact ⟨fun h => h.2, fun h => ⟨le_top, h⟩⟩


end XMod

section ToMulSub

variable {K : Subgroup (GLV V)} {U C L I J M : Submodule (ZMod 2) V}


end ToMulSub

section Local

variable {K : Subgroup (GLV V)} {U : Submodule (ZMod 2) V}

theorem subToSubgroup_conjSub (g : GLV V) (U : Submodule (ZMod 2) V) :
    subToSubgroup (conjSub g U) = g • subToSubgroup U := by
  ext q
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_subToSubgroup, mem_subToSubgroup,
    mem_conjSub]
  rfl

theorem subToSubgroup_conjSub_toMulSub (g : GLV V) (U : Submodule (ZMod 2) V) :
    subToSubgroup (conjSub g U) = (subToSubgroup U).map (linEquivMulAut g).toMonoidHom := by
  rw [subToSubgroup_conjSub]
  ext q
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨g⁻¹ • q, h, by simp⟩
  · rintro ⟨p, hp, rfl⟩
    simpa using hp


theorem commV_toMulSub (K : Subgroup (GLV V)) :
    commV (toMulSub K) = subToSubgroup (commSpace K ⊤) := by
  rw [commSpace, subToSubgroup_span, commV]
  congr 1
  ext c
  constructor
  · rintro ⟨f, hf, q, rfl⟩
    obtain ⟨g, rfl⟩ := linEquivMulAut.surjective f
    refine ⟨g (Multiplicative.toAdd q) - Multiplicative.toAdd q,
      ⟨g, linEquivMulAut_mem_toMulSub.1 hf, Multiplicative.toAdd q, Submodule.mem_top, rfl⟩, ?_⟩
    exact (smul_mul_inv_eq g (Multiplicative.toAdd q)).symm
  · rintro ⟨_, ⟨k, hk, u, -, rfl⟩, rfl⟩
    exact ⟨linEquivMulAut k, linEquivMulAut_mem_toMulSub.2 hk, Multiplicative.ofAdd u,
      smul_mul_inv_eq k u⟩

end Local

section Card

theorem natCard_subToSubgroup (U : Submodule (ZMod 2) V) :
    Nat.card (subToSubgroup U) = Nat.card U :=
  Nat.card_congr (Multiplicative.toAdd.subtypeEquiv fun _ => Iff.rfl)

theorem natCard_eq_two_pow_finrank [Finite V] (U : Submodule (ZMod 2) V) :
    Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
  have : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U), Nat.card_zmod]

theorem natCard_subToSubgroup_eq [Finite V] (U : Submodule (ZMod 2) V) :
    Nat.card (subToSubgroup U) = 2 ^ Module.finrank (ZMod 2) U := by
  rw [natCard_subToSubgroup, natCard_eq_two_pow_finrank]

theorem natCard_subToSubgroup_le_iff [Finite V] (U : Submodule (ZMod 2) V) (n : ℕ) :
    Nat.card (subToSubgroup U) ≤ 2 ^ n ↔ Module.finrank (ZMod 2) U ≤ n := by
  rw [natCard_subToSubgroup_eq]
  exact Nat.pow_le_pow_iff_right (by norm_num)

theorem natCard_subToSubgroup_eq_iff [Finite V] (U : Submodule (ZMod 2) V) (n : ℕ) :
    Nat.card (subToSubgroup U) = 2 ^ n ↔ Module.finrank (ZMod 2) U = n := by
  rw [natCard_subToSubgroup_eq]
  exact Nat.pow_right_inj (by norm_num)

theorem commSpace_zpowers_top (a : GLV V) :
    commSpace (Subgroup.zpowers a) ⊤ = LinearMap.range ((a : V →ₗ[ZMod 2] V) - LinearMap.id) := by
  set R := LinearMap.range ((a : V →ₗ[ZMod 2] V) - LinearMap.id) with hR
  have haR : ∀ w : V, a w - w ∈ R := fun w => ⟨w, by simp⟩
  let S : Subgroup (GLV V) :=
    { carrier := {k | ∀ u, k u - u ∈ R}
      mul_mem' := fun {k k'} hk hk' u => by
        have : (k * k') u - u = (k (k' u) - k' u) + (k' u - u) := by
          show k (k' u) - u = _
          abel
        rw [this]
        exact R.add_mem (hk _) (hk' u)
      one_mem' := fun u => by
        simp
      inv_mem' := fun {k} hk u => by
        have h1 : k⁻¹ u - u = -(k (k⁻¹ u) - k⁻¹ u) := by
          have : k (k⁻¹ u) = u := by simp
          rw [this]
          abel
        rw [h1]
        exact R.neg_mem (hk _) }
  have hS : Subgroup.zpowers a ≤ S := by
    rw [Subgroup.zpowers_le]
    exact haR
  apply le_antisymm
  · rw [commSpace_le_iff]
    intro k hk u _
    exact hS hk u
  · rintro _ ⟨w, rfl⟩
    have : (a : V →ₗ[ZMod 2] V) w - w ∈ commSpace (Subgroup.zpowers a) ⊤ :=
      sub_mem_commSpace (Subgroup.mem_zpowers a) Submodule.mem_top
    simpa using this

theorem commV_zpowers_toMulSub (a : GLV V) :
    commV (Subgroup.zpowers (linEquivMulAut a)) =
      subToSubgroup (LinearMap.range ((a : V →ₗ[ZMod 2] V) - LinearMap.id)) := by
  have h1 : Subgroup.zpowers (linEquivMulAut a) = toMulSub (Subgroup.zpowers a) :=
    (MonoidHom.map_zpowers linEquivMulAut.toMonoidHom a).symm
  rw [h1, commV_toMulSub, commSpace_zpowers_top]

end Card

section HIsoApi

variable {K : Subgroup (GLV V)} {I J M : Submodule (ZMod 2) V}

theorem HIso.refl (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : HIso K I I :=
  ⟨LinearEquiv.refl _ _, fun _ _ _ _ h => h⟩

theorem HIso.trans (h : HIso K I J) (h' : HIso K J M) : HIso K I M := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨ψ, hψ⟩ := h'
  exact ⟨φ.trans ψ, fun k hk i j hij => hψ k hk (φ i) (φ j) (hφ k hk i j hij)⟩

theorem HIso.symm (hI : Invariant K I) (h : HIso K I J) : HIso K J I := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.symm, fun k hk i j hij => ?_⟩
  set x : I := φ.symm i with hx
  have hy : k (x : V) ∈ I := hI k hk _ x.2
  have h1 := hφ k hk x ⟨k (x : V), hy⟩ rfl
  have h2 : ((φ ⟨k (x : V), hy⟩ : J) : V) = (j : V) := by
    rw [← h1]
    have : ((φ x : J) : V) = (i : V) := by rw [hx, LinearEquiv.apply_symm_apply]
    rw [this]
    exact hij
  have h3 : φ ⟨k (x : V), hy⟩ = j := Subtype.ext h2
  have h4 : (⟨k (x : V), hy⟩ : I) = φ.symm j := by
    rw [← h3, LinearEquiv.symm_apply_apply]
  exact congrArg Subtype.val h4

theorem HIso.finrank_eq (h : HIso K I J) :
    Module.finrank (ZMod 2) I = Module.finrank (ZMod 2) J := by
  obtain ⟨φ, -⟩ := h
  exact φ.finrank_eq


end HIsoApi

end G11

end CFSG.Quasithin
