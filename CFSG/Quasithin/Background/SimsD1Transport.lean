module

public import CFSG.Quasithin.Background.SimsD1Embed
public import CFSG.Quasithin.Background.SimsD1TransGrp
public import CFSG.Quasithin.Background.SimsD1TransMod

public section

namespace CFSG.Quasithin.SimsD1.Transport

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique


theorem commutator_le_of_le {G : Type} [Group G] {H X Y : Subgroup G} (hX : X ≤ H)
    (hY : Y ≤ H) : ⁅X, Y⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem (hX hx) (hY hy)) (H.inv_mem (hX hx))) (H.inv_mem (hY hy))


section Img

variable {G F : Type} [Group G] [Group F] {H : Subgroup G}

@[expose] def img (ι : ↥H →* F) (X : Subgroup G) : Subgroup F := (X.subgroupOf H).map ι

theorem exists_map_subtype {X : Subgroup G} (hX : X ≤ H) :
    ∃ Y : Subgroup ↥H, Y.map H.subtype = X :=
  ⟨X.subgroupOf H, Subgroup.map_subgroupOf_eq_of_le hX⟩

theorem img_map_subtype (ι : ↥H →* F) (Y : Subgroup ↥H) : img ι (Y.map H.subtype) = Y.map ι :=
  congrArg (Subgroup.map ι) (Subgroup.comap_map_eq_self_of_injective H.subtype_injective Y)

variable {ι : ↥H →* F}

theorem img_le_img_iff (hι : Function.Injective ι) {X Y : Subgroup G} (hX : X ≤ H) :
    img ι X ≤ img ι Y ↔ X ≤ Y := by
  obtain ⟨X, rfl⟩ := exists_map_subtype hX
  rw [img_map_subtype, img, Subgroup.map_le_map_iff_of_injective hι,
    Subgroup.map_le_iff_le_comap]
  rfl


theorem img_inj (hι : Function.Injective ι) {X Y : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) :
    img ι X = img ι Y ↔ X = Y := by
  refine ⟨fun h => le_antisymm ((img_le_img_iff hι hX).1 h.le) ((img_le_img_iff hι hY).1 h.ge),
    fun h => h ▸ rfl⟩


theorem le_normalizer_img_iff (hι : Function.Injective ι) {K X : Subgroup G} (hK : K ≤ H)
    (hX : X ≤ H) :
    img ι K ≤ Subgroup.normalizer ((img ι X : Subgroup F) : Set F) ↔
      K ≤ Subgroup.normalizer (X : Set G) := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  obtain ⟨X, rfl⟩ := exists_map_subtype hX
  rw [img_map_subtype, img_map_subtype, TransGrp.le_normalizer_map_iff _ hι,
    TransGrp.le_normalizer_map_iff _ H.subtype_injective]


end Img

section Emb


end Emb

end CFSG.Quasithin.SimsD1.Transport
