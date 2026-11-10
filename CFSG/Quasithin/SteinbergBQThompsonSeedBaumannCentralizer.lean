module

public import CFSG.Quasithin.Background.BlueprintB2Thompson
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.Quasithin.Background.BlueprintB2Defs

public section

namespace CFSG.Quasithin.SteinbergBQ

open CFSG CFSG.Quasithin.BlueprintB2


theorem pRank_congr_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (p : ℕ) :
    CFSG.pRank p X = CFSG.pRank p Y := CFSG.pRank_congr_of_mulEquiv e p

theorem map_mem_elemThompsonFamily_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {p : ℕ} {A : Subgroup X} (hA : A ∈ elemThompsonFamily X p) :
    A.map e.toMonoidHom ∈ elemThompsonFamily Y p :=
  ⟨isElementaryAbelian_map hA.1 e.toMonoidHom, by
    rw [Subgroup.card_map_of_injective e.injective, hA.2, pRank_congr_mulEquiv e p]⟩

theorem map_elemThompson_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (p : ℕ) :
    (elemThompson X p).map e.toMonoidHom = elemThompson Y p := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (map_mem_elemThompsonFamily_mulEquiv e hA)
  · refine sSup_le fun B hB => ?_
    intro y hy
    have : e.symm y ∈ elemThompson X p :=
      le_sSup (map_mem_elemThompsonFamily_mulEquiv e.symm hB) ⟨y, hy, rfl⟩
    exact ⟨e.symm y, this, e.apply_symm_apply y⟩

variable {G : Type*} [Group G]

theorem map_elemThompson_subtype_eq_of_le [Finite G] {p : ℕ} [Fact p.Prime]
    {X Y : Subgroup G} (hXY : X ≤ Y) (hJ : (elemThompson Y p).map Y.subtype ≤ X) :
    (elemThompson X p).map X.subtype = (elemThompson Y p).map Y.subtype := by
  have hJZ : elemThompson Y p ≤ X.subgroupOf Y := fun y hy =>
    Subgroup.mem_subgroupOf.2 (hJ ⟨y, hy, rfl⟩)
  have h1 := elemThompson_map_subtype (p := p) hJZ
  let e : X.subgroupOf Y ≃* X := Subgroup.subgroupOfEquivOfLe hXY
  have hcomp : X.subtype.comp e.toMonoidHom = Y.subtype.comp (X.subgroupOf Y).subtype := by
    ext
    rfl
  rw [← map_elemThompson_mulEquiv e p, Subgroup.map_map, hcomp, ← Subgroup.map_map, h1]


theorem mem_map_elemThompsonCenterTorsion_iff [Finite G] {p : ℕ} [Fact p.Prime]
    {X : Subgroup G} {x : G} :
    x ∈ (elemThompsonCenterTorsion X p).map X.subtype ↔
      x ∈ X ∧ x ^ p = 1 ∧ ∀ j ∈ (elemThompson X p).map X.subtype, j * x = x * j := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hc, hp⟩ := mem_elemThompsonCenterTorsion_iff_centralizer.mp hy
    refine ⟨y.2, by simpa using congrArg Subtype.val hp, ?_⟩
    rintro _ ⟨j, hj, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc j hj)
  · rintro ⟨hxX, hxp, hxj⟩
    refine ⟨⟨x, hxX⟩, mem_elemThompsonCenterTorsion_iff_centralizer.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Subgroup.mem_centralizer_iff.mpr fun j hj => Subtype.ext (hxj j ⟨j, hj, rfl⟩)
    · exact Subtype.ext (by simpa using hxp)


end CFSG.Quasithin.SteinbergBQ
