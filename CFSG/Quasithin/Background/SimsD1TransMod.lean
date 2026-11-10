module

public import CFSG.Quasithin.Background.D1Statement
public import CFSG.Quasithin.Background.D2Transport
public import CFSG.Quasithin.Background.ElemAbTransport

public section

namespace CFSG.Quasithin.SimsD1.TransMod

open CFSG.Open CFSG.Quasithin

section Iso

theorem coe_conjAct_apply {G : Type*} [Group G] (V : Subgroup G)
    (g : Subgroup.normalizer (V : Set G)) (v : V) :
    ((conjAct V g v : V) : G) = g * v * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl g) v

theorem congr_symm_comp_congr {V V' : Type*} [Group V] [Group V'] (e : V ≃* V') :
    (MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
      MonoidHom.id (MulAut V) := by
  ext x
  simp


theorem isFFModule_map_congr {W W' : Type*} [CommGroup W] [CommGroup W'] (φ : W ≃* W')
    {X : Subgroup (MulAut W)} (h : IsFFModule X) :
    IsFFModule (X.map (MulAut.congr φ).toMonoidHom) := by
  obtain ⟨A, hAX, hA1, hAel, hcard⟩ := h
  have hinj : Function.Injective (MulAut.congr φ).toMonoidHom := (MulAut.congr φ).injective
  refine ⟨A.map (MulAut.congr φ).toMonoidHom, Subgroup.map_mono hAX,
    fun h => hA1 ((Subgroup.map_eq_bot_iff_of_injective A hinj).1 h),
    (FixVLat.isElemAbelian2_map_congr_iff φ).2 hAel, ?_⟩
  rw [fixV_map_congr_equiv, Subgroup.card_map_of_injective hinj,
    Subgroup.card_map_of_injective φ.injective, Nat.card_congr φ.toEquiv.symm]
  exact hcard

theorem isFFModule_map_congr_iff {W W' : Type*} [CommGroup W] [CommGroup W'] (φ : W ≃* W')
    {X : Subgroup (MulAut W)} :
    IsFFModule (X.map (MulAut.congr φ).toMonoidHom) ↔ IsFFModule X := by
  refine ⟨fun h => ?_, isFFModule_map_congr φ⟩
  have h' := isFFModule_map_congr φ.symm h
  rwa [Subgroup.map_map, congr_symm_comp_congr, Subgroup.map_id] at h'


end Iso

section Injective

variable {A B : Type*} [Group A] [Group B] (f : A →* B)


theorem map_mem_normalizer_iff (hf : Function.Injective f) (V : Subgroup A) (h : A) :
    f h ∈ Subgroup.normalizer ((V.map f : Subgroup B) : Set B) ↔
      h ∈ Subgroup.normalizer (V : Set A) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro H a
    refine (Subgroup.mem_map_iff_mem hf).symm.trans ((H (f a)).trans ?_)
    simp only [← map_inv, ← map_mul]
    exact Subgroup.mem_map_iff_mem hf
  · intro H x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨h * a * h⁻¹, (H a).1 ha, by simp⟩
    · rintro ⟨b, hb, hbx⟩
      refine ⟨h⁻¹ * b * h, (H (h⁻¹ * b * h)).2 (by simpa [mul_assoc] using hb), ?_⟩
      simp only [map_mul, map_inv, hbx]
      group


theorem congr_conjAct_map (hf : Function.Injective f) (V : Subgroup A) {h : A}
    (hh : h ∈ Subgroup.normalizer (V : Set A)) :
    MulAut.congr (V.equivMapOfInjective f hf) (conjAct V ⟨h, hh⟩) =
      conjAct (V.map f) ⟨f h, (map_mem_normalizer_iff f hf V h).2 hh⟩ := by
  ext w
  obtain ⟨v, rfl⟩ := (V.equivMapOfInjective f hf).surjective w
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [coe_conjAct_apply]
  show f ((conjAct V ⟨h, hh⟩ v : V) : A) = _
  rw [coe_conjAct_apply]
  simp

theorem autOn_map (hf : Function.Injective f) (H V : Subgroup A) :
    autOn (H.map f) (V.map f) =
      (autOn H V).map (MulAut.congr (V.equivMapOfInjective f hf)).toMonoidHom := by
  ext σ
  simp only [autOn, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨⟨x, hxN⟩, hxH, rfl⟩
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hxH
    have hhN : h ∈ Subgroup.normalizer (V : Set A) := (map_mem_normalizer_iff f hf V h).1 hxN
    exact ⟨conjAct V ⟨h, hhN⟩, ⟨⟨h, hhN⟩, hh, rfl⟩, congr_conjAct_map f hf V hhN⟩
  · rintro ⟨_, ⟨⟨h, hhN⟩, hh, rfl⟩, rfl⟩
    exact ⟨⟨f h, (map_mem_normalizer_iff f hf V h).2 hhN⟩, ⟨h, hh, rfl⟩,
      (congr_conjAct_map f hf V hhN).symm⟩


end Injective

end CFSG.Quasithin.SimsD1.TransMod
