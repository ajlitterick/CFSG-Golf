module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralizerQuotient

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open

variable {G : Type*} [Group G]


theorem localHull_image (u z : G) :
    (localHull u z).map (localCentralizer u).subtype =
      Subgroup.closure (conjugatesOf z ∩ (localCentralizer u : Set G)) := by
  rw [localHull, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha, a.property⟩
  · rintro ⟨hxz, hxX⟩
    exact ⟨⟨x, hxX⟩, hxz, rfl⟩


end CFSG.ShultStronglyClosedTI
