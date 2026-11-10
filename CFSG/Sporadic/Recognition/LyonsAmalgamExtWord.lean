module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Data.Fin.VecNotation

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

variable {ι : Type*} {X X₀ : Type*} [Group X] [Group X₀]

theorem map_lift_eq_lift_comp (φ : X →* X₀) (g : ι → X) (r : FreeGroup ι) :
    φ (FreeGroup.lift g r) = FreeGroup.lift (φ ∘ g) r := by
  have h : φ.comp (FreeGroup.lift g) = FreeGroup.lift (φ ∘ g) :=
    FreeGroup.ext_hom _ _ fun i => by simp
  exact congrArg (fun f : FreeGroup ι →* X₀ => f r) h


theorem lift_eq_one_iff_lift_comp_eq_one_of_injective {φ : X →* X₀} (hφ : Function.Injective φ)
    (g : ι → X) (r : FreeGroup ι) :
    FreeGroup.lift g r = 1 ↔ FreeGroup.lift (φ ∘ g) r = 1 := by
  rw [← map_lift_eq_lift_comp, ← map_one φ, hφ.eq_iff]

theorem lift_eq_one_iff_lift_comp_eq_one (φ : X ≃* X₀) (g : ι → X) (r : FreeGroup ι) :
    FreeGroup.lift g r = 1 ↔ FreeGroup.lift (φ ∘ g) r = 1 :=
  lift_eq_one_iff_lift_comp_eq_one_of_injective (φ := φ.toMonoidHom) φ.injective g r


section Subgroup

variable (H : Subgroup X)

theorem coe_lift_subgroup (g : ι → H) (r : FreeGroup ι) :
    ((FreeGroup.lift g r : H) : X) = FreeGroup.lift (fun i => (g i : X)) r := by
  have h : H.subtype.comp (FreeGroup.lift g) = FreeGroup.lift (fun i => (g i : X)) :=
    FreeGroup.ext_hom _ _ fun i => by simp
  exact congrArg (fun f : FreeGroup ι →* X => f r) h

theorem lift_subgroup_eq_one_iff (g : ι → H) (r : FreeGroup ι) :
    FreeGroup.lift g r = 1 ↔ FreeGroup.lift (fun i => (g i : X)) r = 1 := by
  rw [← coe_lift_subgroup, ← H.coe_one, Subtype.coe_inj]


end Subgroup

end CFSG.Sporadic.Recognition.LyonsSims
