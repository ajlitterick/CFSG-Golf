module

public import CFSG.Quasithin.H13.NParamLiftS5
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.E1.LiftS5

open CFSG.Open Equiv CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

@[expose] def RootFourLift (H T : Subgroup G) (ψ : ↥H →* Perm (Fin 5)) : Prop :=
  ∃ A : Subgroup G, A ≤ T ∧ IsElemAbelian 2 A ∧
    (A.subgroupOf H).map ψ ≤ alternatingGroup (Fin 5) ∧ Nat.card ↥((A.subgroupOf H).map ψ) = 4

theorem one_lt_nParam_of_rootFourLift {H T : Subgroup G} {ψ : ↥H →* Perm (Fin 5)}
    (hA5 : alternatingGroup (Fin 5) ≤ ψ.range) (hT : IsSylowIn 2 T H)
    (h : RootFourLift H T ψ) : 1 < E1.nParam H := by
  obtain ⟨A, hAT, hA, hψA, hψA4⟩ := h
  exact one_lt_nParam_of_lift ψ hA5 hT hAT hA hψA hψA4

@[expose] noncomputable def autAltFive : Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
  MulEquiv.ofBijective MulAut.conjNormal
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num))

theorem autAltFive_apply (σ : Perm (Fin 5)) : autAltFive σ = MulAut.conjNormal σ := rfl

@[expose] noncomputable def quotAut (K : Subgroup G) :
    MulAut ↥K →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) where
  toFun α := QuotientGroup.congr _ _ α
    (Subgroup.characteristic_iff_map_eq.mp inferInstance α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

@[expose] noncomputable def quotConj (K : Subgroup G) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
  (quotAut K).comp K.normalizerMonoidHom

omit [Finite G] in
theorem quotConj_of_mem (K : Subgroup G) (g : ↥(Subgroup.normalizer (K : Set G)))
    (hg : (g : G) ∈ K) :
    quotConj K g = MulAut.conj (QuotientGroup.mk ⟨g, hg⟩ : ↥K ⧸ CFSG.pCore 2 ↥K) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H k =>
    rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    exact Subgroup.normalizerMonoidHom_apply_apply_coe K g k

@[expose] noncomputable def quotPerm {H K : Subgroup G} (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) : ↥H →* Perm (Fin 5) :=
  autAltFive.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp ((quotConj K).comp (Subgroup.inclusion hHK)))

omit [Finite G] in
theorem quotPerm_of_mem {H K : Subgroup G} (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) (h : ↥H) (hk : (h : G) ∈ K) :
    quotPerm hHK e h = ((e (QuotientGroup.mk ⟨h, hk⟩) : alternatingGroup (Fin 5)) :
      Perm (Fin 5)) := by
  have hk' : ((Subgroup.inclusion hHK h : ↥(Subgroup.normalizer (K : Set G))) : G) ∈ K := by
    simpa using hk
  have he : (⟨_, hk'⟩ : ↥K) = ⟨h, hk⟩ := Subtype.ext (by simp)
  apply autAltFive.injective
  have h1 : autAltFive (quotPerm hHK e h) =
      MulAut.congr e (quotConj K (Subgroup.inclusion hHK h)) := by
    simp only [quotPerm, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  rw [h1, quotConj_of_mem K _ hk', he]
  refine MulEquiv.ext fun a => Subtype.ext ?_
  rw [autAltFive_apply, MulAut.conjNormal_apply]
  simp [MulAut.congr_apply, MulAut.conj_apply]

omit [Finite G] in
theorem alt_le_range_quotPerm {H K : Subgroup G} (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hKH : K ≤ H) (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) :
    alternatingGroup (Fin 5) ≤ (quotPerm hHK e).range := by
  intro σ hσ
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm ⟨σ, hσ⟩)
  refine ⟨⟨k, hKH k.2⟩, ?_⟩
  rw [quotPerm_of_mem hHK e _ k.2]
  have : (QuotientGroup.mk ⟨(k : G), k.2⟩ : ↥K ⧸ CFSG.pCore 2 ↥K) = e.symm ⟨σ, hσ⟩ := hk
  rw [this, MulEquiv.apply_symm_apply]

@[expose] def RootFourLiftQuot (T K : Subgroup G) : Prop :=
  ∃ A : Subgroup G, A ≤ T ∧ A ≤ K ∧ IsElemAbelian 2 A ∧
    Nat.card ↥((A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) = 4

omit [Finite G] in
theorem rootFourLift_of_quot {H T K : Subgroup G} (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hKH : K ≤ H) (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))
    (h : RootFourLiftQuot T K) : RootFourLift H T (quotPerm hHK e) := by
  obtain ⟨A, hAT, hAK, hA, h4⟩ := h
  set j : (↥K ⧸ CFSG.pCore 2 ↥K) →* Perm (Fin 5) :=
    (alternatingGroup (Fin 5)).subtype.comp e.toMonoidHom with hj
  have hjinj : Function.Injective j := fun x y hxy =>
    e.injective (Subtype.ext (by simpa [hj] using hxy))
  have himg : (A.subgroupOf H).map (quotPerm hHK e) =
      ((A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map j := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyK : (y : G) ∈ K := hAK hy
      refine ⟨QuotientGroup.mk ⟨y, hyK⟩, ⟨⟨y, hyK⟩, hy, rfl⟩, ?_⟩
      rw [quotPerm_of_mem hHK e y hyK]
      rfl
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨⟨y, hKH y.2⟩, hy, ?_⟩
      rw [quotPerm_of_mem hHK e _ y.2]
      rfl
  refine ⟨A, hAT, hA, ?_, ?_⟩
  · rw [himg]
    rintro _ ⟨x, -, rfl⟩
    exact (e x).2
  · rw [himg, Subgroup.card_map_of_injective hjinj, h4]

theorem one_lt_nParam_of_rootFourLiftQuot {H T K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hKH : K ≤ H)
    (hA5 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hT : IsSylowIn 2 T H) (h : RootFourLiftQuot T K) : 1 < E1.nParam H := by
  obtain ⟨e⟩ := hA5
  exact one_lt_nParam_of_rootFourLift (alt_le_range_quotPerm hHK hKH e) hT
    (rootFourLift_of_quot hHK hKH e h)

open E1 A1b


theorem card_map_dvd_card_map_mk {K Q : Type*} [Group K] [Group Q] (φ : K →* Q) (N : Subgroup K)
    [N.Normal] (hN : N ≤ φ.ker) (B : Subgroup K) :
    Nat.card ↥(B.map φ) ∣ Nat.card ↥(B.map (QuotientGroup.mk' N)) := by
  have hcomp : (QuotientGroup.lift N φ hN).comp (QuotientGroup.mk' N) = φ := by
    ext x; simp
  have h1 : (B.map (QuotientGroup.mk' N)).map (QuotientGroup.lift N φ hN) = B.map φ := by
    rw [Subgroup.map_map, hcomp]
  rw [← h1]
  exact Subgroup.card_map_dvd (H := B.map (QuotientGroup.mk' N)) (QuotientGroup.lift N φ hN)


end CFSG.Quasithin.E1.LiftS5
