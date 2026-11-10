module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossFamilies
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted
import CFSG.RankThree.PartOne.S12K.Rigidity
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
import CFSG.LieType.Ree.LargeReeEightTorus
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

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

private theorem exists_reeF4_of_isReeF4 {d : TauCeti.LieTypeIndex} (h : I294CrossIsReeF4 d) :
    ∃ m : ℕ, d = .reeF4 m := by
  cases d <;> first
    | exact ⟨_, rfl⟩
    | exact False.elim h
    | simp [I294CrossIsReeF4] at h

private theorem three_pow_four_dvd_ordTwistedF4 {f : ℕ} (hf : Odd f) (h3 : 3 ∣ f) :
    3 ^ 4 ∣ CFSG.Open.ordTwistedF4 (2 ^ f) := by
  obtain ⟨k, rfl⟩ := h3
  have hk : Odd k := (Nat.odd_mul.1 hf).2
  have hkpos : 0 < k := hk.pos
  have hq : (2 : ℕ) ^ (3 * k) = 8 ^ k := by
    rw [pow_mul]
    norm_num
  have h9 : 9 ∣ 2 ^ (3 * k) + 1 := by
    rw [hq]
    simpa using (Odd.nat_add_dvd_pow_add_pow 8 1 hk : (8 : ℕ) + 1 ∣ 8 ^ k + 1 ^ k)
  have h81 : 3 ^ 4 ∣ (2 ^ (3 * k) + 1) ^ 2 := by
    have h := pow_dvd_pow_of_dvd h9 2
    rwa [show (9 : ℕ) ^ 2 = 3 ^ 4 by norm_num] at h
  have h2 : 2 ≤ 2 ^ (3 * k) := Nat.le_self_pow (by omega) 2
  rw [CFSG.RankThree.PartOne.S12K.ordTwistedF4_eq_factored h2]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
    (dvd_mul_of_dvd_right h81 _) _) _) _

theorem i294CrossThreeRankTwoOn_ReeF4 :
    I294CrossThreeRankTwoOn I294CrossIsReeF4 := by
  intro L _ _ _ _ d hd _ he _ _ _ hnot3 α hα
  obtain ⟨d, hv⟩ := d
  obtain ⟨m, rfl⟩ := exists_reeF4_of_isReeF4 hd
  obtain ⟨e⟩ := he
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index m hv e
  obtain ⟨-, -, -, -, hcardO, -, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_model_field_outer_group_and_inner_involutions
      L 2 (2 * m + 1) hR
  have hord : Nat.card L = CFSG.Open.ordTwistedF4 (2 ^ (2 * m + 1)) :=
    CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 hR
  have h3nd : ¬ 3 ∣ 2 * m + 1 := fun h3 =>
    hnot3 (by rw [hord]; exact three_pow_four_dvd_ordTwistedF4 ⟨m, rfl⟩ h3)
  obtain ⟨k, hk⟩ := hα
  have hxk : (QuotientGroup.mk' (inner L) α : Outer L) ^ 3 ^ k = 1 := by
    rw [← map_pow, hk, map_one]
  have hdvd3 : orderOf (QuotientGroup.mk' (inner L) α : Outer L) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one hxk
  have hdvdf : orderOf (QuotientGroup.mk' (inner L) α : Outer L) ∣ 2 * m + 1 := by
    have h := orderOf_dvd_natCard (QuotientGroup.mk' (inner L) α : Outer L)
    rwa [hcardO] at h
  have hcop : Nat.Coprime (3 ^ k) (2 * m + 1) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3nd)
  have h1 : orderOf (QuotientGroup.mk' (inner L) α : Outer L) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd3 hcop) hdvdf
  exact (QuotientGroup.eq_one_iff (N := inner L) α).1 (orderOf_eq_one_iff.1 h1)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
