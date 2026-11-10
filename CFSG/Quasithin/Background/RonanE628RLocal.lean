module

public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.C126NatDProd
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Background.E6Hyp
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.RonanE628

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.E6
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T M V : Subgroup G}

theorem exists_central_of_normalized {T V : Subgroup G} (hT : IsPGroup 2 ↥T) (hVT : V ≤ T)
    (hV : V ≠ ⊥) (hTV : T ≤ Subgroup.normalizer (V : Set G)) :
    ∃ v ∈ V, v ≠ 1 ∧ ∀ t ∈ T, t * v = v * t := by
  classical
  have hnil : Group.IsNilpotent ↥T := hT.isNilpotent
  have hVn : (V.subgroupOf T).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVT).mpr hTV
  have hV1 : V.subgroupOf T ≠ ⊥ := by
    intro hb
    apply hV
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hVT hx⟩ : ↥T) ∈ V.subgroupOf T := hx
    rw [hb, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hV1
  obtain ⟨⟨⟨v, hvT⟩, hvmem⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hcen
  refine ⟨v, Subgroup.mem_subgroupOf.mp hvmem.1, fun h => hv1 (Subtype.ext (Subtype.ext h)),
    fun t ht => ?_⟩
  have := Subgroup.mem_center_iff.mp hvmem.2 ⟨t, ht⟩
  exact congrArg Subtype.val this


section HStar


end HStar


end CFSG.Quasithin.RonanE628
