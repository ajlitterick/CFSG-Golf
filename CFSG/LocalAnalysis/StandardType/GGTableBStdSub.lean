module

public import CFSG.LocalAnalysis.StandardType.GGTableBBstar
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

section Fix

variable {H : Type*} [Group H]

@[expose] def ggFix (a : MulAut H) : Subgroup H where
  carrier := {h | a h = h}
  mul_mem' {x y} hx hy := by
    change a x = x at hx
    change a y = y at hy
    change a (x * y) = x * y
    rw [map_mul, hx, hy]
  one_mem' := map_one a
  inv_mem' {x} hx := by
    change a x = x at hx
    change a x⁻¹ = x⁻¹
    rw [map_inv, hx]

theorem mem_ggFix {a : MulAut H} {h : H} : h ∈ ggFix a ↔ a h = h :=
  Iff.rfl

end Fix

section Inj

variable {H H' : Type*} [Group H] [Group H']

theorem isSubnormal_comap_hom (f : H →* H') {A B : Subgroup H'} (h : IsSubnormal A B) :
    IsSubnormal (A.comap f) (B.comap f) :=
  h.comap f

theorem isComponentOf_map_of_injective (f : H →* H') (hf : Function.Injective f)
    {K C : Subgroup H} (h : IsComponentOf K C) : IsComponentOf (K.map f) (C.map f) := by
  obtain ⟨hKC, hs, hq⟩ := h
  refine ⟨Subgroup.map_mono hKC, isSubnormal_map_hom f hs, ?_⟩
  rw [CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native] at hq ⊢
  exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
    (K.equivMapOfInjective f hf)).1 hq

theorem isComponentOf_comap_of_injective (f : H →* H') (hf : Function.Injective f)
    {K' : Subgroup H'} {C : Subgroup H} (h : IsComponentOf K' (C.map f)) :
    IsComponentOf (K'.comap f) C ∧ (K'.comap f).map f = K' := by
  obtain ⟨hKC, hs, hq⟩ := h
  have hmap : (K'.comap f).map f = K' :=
    Subgroup.map_comap_eq_self (hKC.trans (Subgroup.map_le_range f C))
  refine ⟨⟨?_, ?_, ?_⟩, hmap⟩
  · intro g hg
    obtain ⟨g', hg', hgg'⟩ := hKC hg
    rw [← hf hgg']
    exact hg'
  · have := isSubnormal_comap_hom f hs
    rwa [Subgroup.comap_map_eq_self_of_injective hf] at this
  · rw [CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native] at hq ⊢
    have e : ↥(K'.comap f) ≃* ↥K' :=
      ((K'.comap f).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hmap)
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 hq

theorem largeEvenLayer_map_of_injective (f : H →* H') (hf : Function.Injective f)
    (C : Subgroup H) : LargeEvenLayer (C.map f) = (LargeEvenLayer C).map f := by
  apply le_antisymm
  · refine sSup_le fun K' hK' => ?_
    obtain ⟨hK, hmap⟩ := isComponentOf_comap_of_injective f hf hK'
    rw [← hmap]
    exact Subgroup.map_mono (le_sSup hK)
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (isComponentOf_map_of_injective f hf hK)

end Inj

section Gamma

variable {G : Type} [Group G] (L : Subgroup G) {B : Subgroup G}
  (hBN : B ≤ Subgroup.normalizer (L : Set G))

@[expose] noncomputable def ggGamma : B →* MulAut L :=
  L.normalizerMonoidHom.comp (Subgroup.inclusion hBN)

theorem ggGamma_coe (b : B) (l : L) : ((ggGamma L hBN b l : L) : G) = b * l * (b : G)⁻¹ :=
  rfl

theorem ggGamma_eq_one_iff (b : B) :
    ggGamma L hBN b = 1 ↔ (b : G) ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h l hl
    have h1 := congrArg Subtype.val (congrArg (fun a : MulAut L => a ⟨l, hl⟩) h)
    simp only [MulAut.one_apply] at h1
    rw [ggGamma_coe] at h1
    calc l * b = b * l * (b : G)⁻¹ * b := by rw [h1]
      _ = b * l := by group
  · intro h
    ext l
    rw [MulAut.one_apply, ggGamma_coe, ← h l l.2]
    group

theorem ggBeta_ggQuotHom {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) (b : B) (l : L) :
    ggBeta L θ hBN b (ggQuotHom θ l) = ggQuotHom θ (ggGamma L hBN b l) := by
  rw [ggQuotHom_apply, ggQuotHom_apply, ggBeta_eq, ggLAut_apply]
  rfl

theorem map_ggFix_ggGamma (d : B) :
    (ggFix (ggGamma L hBN d)).map L.subtype =
      L ⊓ Subgroup.centralizer ({(d : G)} : Set G) := by
  ext g
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := congrArg Subtype.val (mem_ggFix.mp hl)
    rw [ggGamma_coe] at h1
    calc (l : G) * d = d * l * (d : G)⁻¹ * d := by rw [h1]
      _ = d * l := by group
  · rintro ⟨hgL, hgd⟩
    refine ⟨⟨g, hgL⟩, ?_, rfl⟩
    apply Subtype.ext
    rw [ggGamma_coe]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hgd
    calc (d : G) * g * (d : G)⁻¹ = g * d * (d : G)⁻¹ := by rw [h1]
      _ = g := by group

variable [Finite G]

theorem ker_ggGamma {p : ℕ} (hp : p.Prime) {x : G} (hS : LargeEvenSStar p B x L) :
    (ggGamma L hBN).ker = (Subgroup.zpowers x).subgroupOf B := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff,
    ← inf_centralizer_eq_zpowers_of_sstar hp hS]
  exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩

theorem card_range_ggGamma_mul {p : ℕ} (hp : p.Prime) {x : G} (hS : LargeEvenSStar p B x L) :
    Nat.card (ggGamma L hBN).range * p = Nat.card B := by
  have := Fact.mk hp
  have h1 := card_range_mul_card_ker (ggGamma L hBN)
  rw [ker_ggGamma L hBN hp hS] at h1
  have hxB : x ∈ B := hS.2.1
  have h2 : Nat.card ((Subgroup.zpowers x).subgroupOf B) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxB)).toEquiv,
      Nat.card_zpowers, orderOf_eq_prime (hS.1.1.2 x hxB) hS.2.2.1]
  rwa [h2] at h1

end Gamma

@[expose] def GGEndNode (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
      ∃ a ∈ A, a ≠ 1 ∧ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) ∧
        ∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a)

section Reduction

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_centralizer_sup_zpowers {L : Subgroup G} {x d : G}
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) :
    L ⊓ Subgroup.centralizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers d : Subgroup G) : Set G) =
      L ⊓ Subgroup.centralizer ({d} : Set G) := by
  ext g
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hgL, hg⟩
    refine ⟨hgL, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hg d
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))).symm
  · rintro ⟨hgL, hgd⟩
    refine ⟨hgL, ?_⟩
    have h1 : Subgroup.zpowers x ⊔ Subgroup.zpowers d ≤ Subgroup.centralizer ({g} : Set G) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp (hLx hgL)).symm
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hgd).symm
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (h1 hh)


end Reduction

end CFSG.StandardType
