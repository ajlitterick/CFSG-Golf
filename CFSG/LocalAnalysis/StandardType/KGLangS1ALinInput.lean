module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1KGInputs
import CFSG.LocalAnalysis.StandardType.KGLangS1ALinCont

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem kgLangAxisS1LinInput_holds :
    KGLangAxisS1LinInput := by
  intro p lab hp hp2 hlab hS Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hsix, hsplit, hpn, htag⟩ := hS
  dsimp only at htag
  subst htag
  obtain ⟨hn, -⟩ : 1 ≤ n ∧ (1 ≤ l ∧ (l = 1 → 2 ≤ n)) := hlab
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  exact NbrGraphLinear.recipeLinear_all (d := l + 1) (N := 2 ^ n) (Q₀ := Q)
    (Q := KGLangAxisS1LinCont p)
    (fun F _ _ hF => kgLangS1A_lin_cont hp hp2 (lab := ⟨.A, l, n⟩) ⟨hsix, hsplit, hpn, rfl⟩ hn F
      hF) hQ

end CFSG.StandardType
