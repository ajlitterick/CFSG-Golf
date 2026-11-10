module

public import CFSG.Quasithin.Background.InternalSecFF

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {U W Y : Subgroup G} [IsMulCommutative ↥W]
  [IsMulCommutative ↥U]

omit [Finite G] [IsMulCommutative ↥U] in
theorem autSub_map_le_autOn (hUW : U ≤ W) (hYU : Y ≤ Subgroup.normalizer (U : Set G)) :
    (autSub (autOn Y W) (U.subgroupOf W)).map
        (MulAut.congr (Subgroup.subgroupOfEquivOfLe hUW)).toMonoidHom ≤ autOn Y U := by
  rintro _ ⟨ψ, hψ, rfl⟩
  obtain ⟨g', hg'X, rfl⟩ := mem_autSub.1 hψ
  obtain ⟨g, hgY, hgg'⟩ := Setup.mem_autOn_iff.1 hg'X
  refine Setup.mem_autOn_iff.2 ⟨⟨g, hYU hgY⟩, hgY, ?_⟩
  ext u
  rw [coe_conjAct_apply]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply]
  show (g : G) * u * (g : G)⁻¹ = (((g' : MulAut ↥W) ⟨u, hUW u.2⟩ : ↥W) : G)
  rw [← hgg', coe_conjAct_apply]

theorem isFFModule_autOn_of_offender (hW2 : ∀ w ∈ W, w ^ 2 = 1) (hUW : U ≤ W)
    (hYU : Y ≤ Subgroup.normalizer (U : Set G)) {A : Subgroup (MulAut ↥W)}
    (hA : IsFFStarOffender (autOn Y W) A) (hnt : ¬ A ≤ centSub (U.subgroupOf W)) :
    IsFFModule (autOn Y U) := by
  have hAinv : ∀ a ∈ A, ∀ w ∈ U.subgroupOf W, a w ∈ U.subgroupOf W := by
    intro a ha w hw
    obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 (hA.1 ha)
    rw [Subgroup.mem_subgroupOf, coe_conjAct_apply]
    exact (Subgroup.mem_normalizer_iff.mp (hYU hg) w).mp hw
  have hWA : commSub (U.subgroupOf W) A ≠ ⊥ := by
    intro h
    apply hnt
    intro a ha w hw
    exact (commSub_eq_bot_iff.1 h) hw a ha
  have hoff := B7_1_1 hA hAinv hWA
  have hV : ∀ v : ↥(U.subgroupOf W), v ^ 2 = 1 := fun v =>
    Subtype.ext (Subtype.ext (by simpa using hW2 _ (v : ↥W).2))
  have hne : {B | IsFFStarOffender (autSub (autOn Y W) (U.subgroupOf W)) B}.Nonempty :=
    ⟨_, hoff⟩
  have hFF : IsFFModule (autSub (autOn Y W) (U.subgroupOf W)) :=
    ((B1_4_5 hV (autSub (autOn Y W) (U.subgroupOf W))).out 1 2).2 hne
  exact B1Red.isFFModule_mono (autSub_map_le_autOn hUW hYU)
    (B1Red.isFFModule_map_congr' (Subgroup.subgroupOfEquivOfLe hUW) hFF)


end CFSG.Quasithin.InternalSec
