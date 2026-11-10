module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi23
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporTh
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporLy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporJ3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporSuz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCheck
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporThreeSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporHN3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRu3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporHe3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSRNum

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporFactors sporOrder sporFactors_prime
  sporFactors_nodup exists_of_prime_pow_dvd_prod)


theorem sporOrd_eq_sporOrder (s : TauCeti.SporadicName) :
    CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s = sporOrder s := by
  cases s <;> rfl


theorem row_of_factors
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    {s : TauCeti.SporadicName} (hsB : s ≠ .B) (hsM : s ≠ .M)
    (h : ∀ x ∈ sporFactors s, x.1 ≠ 2 → 2 ≤ x.2 → I1416SporRow s x.1) (p : ℕ) :
    I1416SporRow s p := by
  intro S _ _ he hp hp2
  by_cases hd : p ^ 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s
  · rw [sporOrd_eq_sporOrder] at hd
    obtain ⟨x, hx, rfl, h2⟩ := exists_of_prime_pow_dvd_prod hp (by norm_num)
      (sporFactors_prime s) (sporFactors_nodup s) hd
    exact h x hx hp2 h2 S he hp hp2
  · exact row_of_not_sq_dvd hOut hbr hOrd hsB hsM hp hd S he hp hp2


section HN3


end HN3

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows
