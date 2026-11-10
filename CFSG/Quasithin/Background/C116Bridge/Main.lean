module

public import CFSG.Quasithin.EmptyFaithful.S151S4F

import CFSG.Quasithin.Background.B15P4Layer2Final

public section

namespace CFSG.Quasithin.C116Bridge

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]


theorem isSQTKTC_of_isSQTKIn {X : Subgroup G} (h : IsSQTKIn X) : IsSQTKTC X := by
  exact C1GN.isSQTKTC_iff_sqtkGroup.mpr h


private theorem c116_autI_thompsonJ_le_ffJ {X V S : Subgroup G} (hred : IsTwoReducedIn X V)
    (hS : IsSylowTwoOf S X) : autI hred.2.2.1 (thompsonJ S) ≤ ffJ (autI hred.2.2.1 X) := by
  refine (autI_mono hred.2.2.1 (thompsonJ_le_thompsonJ_of_isSylowTwoOf hS)).trans ?_
  rw [autI_thompsonJ hred.2.2.1 hred.2.1]
  refine iSup_le fun A => iSup_le fun hA => iSup_le fun hAH => ?_
  exact le_iSup₂ (f := fun (B : Subgroup (MulAut (IntMod V hred.2.2.1)))
    (_ : IsFFStarOffender (autI hred.2.2.1 X) B) => B) A
    (offenderImages_isFFStarOffender hred.2.2.1 hred.1 hred.2.1 hA)

theorem thompsonJ_normalizes_components {X V T : Subgroup G} (hred : IsTwoReducedIn X V)
    (hT : IsSylowTwoOf T X) :
    ∀ K : Subgroup (MulAut ↥V), CFSG.Open.IsComponentOf K (autOn X V) →
      autOn (thompsonJ T) V ≤ Subgroup.normalizer (K : Set (MulAut ↥V)) := by
  intro K hK
  have hle : autI hred.2.2.1 (thompsonJ T) ≤ ffJ (autI hred.2.2.1 X) :=
    c116_autI_thompsonJ_le_ffJ hred hT
  have hff : ffJ (autI hred.2.2.1 X) ≤ Subgroup.normalizer (K : Set (MulAut ↥V)) := by
    refine iSup_le fun A => iSup_le fun hA => ?_
    exact CFSG.Quasithin.B15P4.asB15Part4 (IntMod V hred.2.2.1) (fun v => IntMod.sq_eq_one v)
      (autI hred.2.2.1 X) A hA K hK
  exact hle.trans hff


end CFSG.Quasithin.C116Bridge
