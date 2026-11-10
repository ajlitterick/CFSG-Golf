module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossFamilies
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted
public import CFSG.RankThree.PartTwo.KFacts.K71OddChar
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import Certificates.Kernel.J4Count.FixCE
public import CFSG.RankThree.PartTwo.Sec4.Item47
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Walter.W67.Statements
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Weak
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import Certificates.Kernel.J4Count.FixCPairBase1
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Main
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43
public import CFSG.Walter.JRFacts
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma58
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import Lean.Data.Json

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

private theorem eq_tits_of_isTits {d : TauCeti.LieTypeIndex} (h : I294CrossIsTits d) :
    d = .tits := by
  cases d <;> first | rfl | exact False.elim h

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem i294CrossThreeRankTwoOn_Tits :
    I294CrossThreeRankTwoOn I294CrossIsTits := by
  intro L _ _ _ _ d hd _ e _ _ _ _ α hα
  have hdT : d.1 = .tits := eq_tits_of_isTits hd
  obtain ⟨d, hv⟩ := d
  have hd' : d = .tits := hdT
  subst hd'
  obtain ⟨e0⟩ := e
  obtain ⟨h2, -⟩ := CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier L 2 1
    (CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_tits_of_index hv e0)
  obtain ⟨k, hk⟩ := hα
  have hk3 : (α : Outer L) ^ 3 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
  obtain ⟨n, hn⟩ := h2 (α : Outer L)
  have hcop : Nat.Coprime (2 ^ n) (3 ^ k) := Nat.Coprime.pow n k (by norm_num)
  have h1 : orderOf (α : Outer L) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h3 : orderOf (α : Outer L) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk3
  have h4 : orderOf (α : Outer L) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h3
  exact (QuotientGroup.eq_one_iff α).mp (orderOf_eq_one_iff.mp h4)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
