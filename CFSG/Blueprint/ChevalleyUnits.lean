module

public import CFSG.Blueprint.Chevalley

public noncomputable section

namespace CFSG.Blueprint.Chevalley

variable {τ : Tag} {R : Type*} [CommRing R]


private theorem height_single (i : Fin τ.rank) : height (Pi.single i (1 : ℤ)) = 1 := by
  simp [height]

private theorem height_neg_single (i : Fin τ.rank) : height (-Pi.single i (1 : ℤ)) = -1 := by
  simp [height]

private theorem rootVec_of_isRoot {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ R β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 :=
  dite_eq_left hβ


end CFSG.Blueprint.Chevalley
