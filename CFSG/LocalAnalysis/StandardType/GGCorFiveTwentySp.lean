module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Split

variable {G : Type} [Group G]

theorem GGInnerDiagOnLabel.mono_label {S T : ℕ → LargeEvenLabel → Prop} {p : ℕ}
    {Bs L : Subgroup G} (hST : ∀ lab, S p lab → T p lab) (h : GGInnerDiagOnLabel S p Bs L) :
    GGInnerDiagOnLabel T p Bs L :=
  largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hST _ hP.1, hP.2⟩) h

end Split


end CFSG.StandardType

end
