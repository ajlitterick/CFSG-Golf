module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevRecipe
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggFieldFixKnown_E7E8
    : GGFieldFixKnown fun _ lab => lab.tag = .E7 ∨ lab.tag = .E8 := by
  intro p lab hp _ hlab hS
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  rcases hS with ht | ht <;> dsimp only at ht <;> subst ht
  · exact recipeChevalley_and (fun K _ _ hK _ _ f hf hord =>
      chev_fixStd (τ := .E7) (Or.inr (Or.inl rfl)) hn hK hp.pos hf hord) hQ
  · exact recipeChevalley_and (fun K _ _ hK _ _ f hf hord =>
      chev_fixStd (τ := .E8) (Or.inr (Or.inr rfl)) hn hK hp.pos hf hord) hQ

end CFSG.StandardType
