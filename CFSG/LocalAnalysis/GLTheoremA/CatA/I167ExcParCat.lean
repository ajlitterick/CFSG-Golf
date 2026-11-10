module


import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSG.Adapters.TauCetiLieModels
import CFSG.GroupTheory.WeirSylow.CrossRankLinear
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCOrthPlus
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcSylowTorus
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterRoots
public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Rank
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapPair
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThree
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups


private theorem exc_cat_twoPart_aux1 {k j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) :
    Odd ((2 ^ k) ^ j - 1) :=
  CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hk hj

private theorem exc_cat_twoPart_aux2 {a x : ℕ} (hx : Odd x) :
    padicValNat 2 (2 ^ a * x) = a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (by positivity) hx.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd
      (fun hd => Nat.not_even_iff_odd.2 hx (even_iff_two_dvd.2 hd)), Nat.add_zero]

private theorem exc_cat_twoPart_aux3 {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    padicValNat 2 (orderD n (2 ^ k)) = k * (n * (n - 1)) := by
  rw [← Nat.factorization_def (orderD n (2 ^ k)) Nat.prime_two]
  exact CFSG.SeitzReduction.OmegaPilot.factorization_two_ordD hk hn

private theorem exc_cat_twoPart_aux4 (k : ℕ) (hk : 1 ≤ k) :
    orderA 3 (2 ^ k) =
      (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * (((2 ^ k) ^ 3 - 1) * ((2 ^ k) ^ 4 - 1))) := by
  have hodd : Odd ((2 ^ k) - 1) := by
    simpa using exc_cat_twoPart_aux1 (k := k) (j := 1) hk le_rfl
  have hg : Nat.gcd 4 ((2 ^ k) - 1) = 1 :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd)
  unfold orderA
  rw [hg, Nat.div_one]
  have hI : Finset.Icc 2 (3 + 1) = {2, 3, 4} := by decide
  rw [hI, Finset.prod_insert (by decide), Finset.prod_pair (by decide)]

private theorem exc_cat_twoPart_aux5 {k : ℕ} (hk : 1 ≤ k) :
    padicValNat 2 (orderA 3 (2 ^ k)) = k * (3 * (3 - 1)) := by
  rw [exc_cat_twoPart_aux4 k hk]
  have hpow : (2 ^ k) ^ 6 = 2 ^ (6 * k) := by
    rw [← pow_mul]
    ring
  rw [hpow]
  have hA : Odd ((2 ^ k) ^ 2 - 1) := exc_cat_twoPart_aux1 hk (by norm_num)
  have hB : Odd ((2 ^ k) ^ 3 - 1) := exc_cat_twoPart_aux1 hk (by norm_num)
  have hC : Odd ((2 ^ k) ^ 4 - 1) := exc_cat_twoPart_aux1 hk (by norm_num)
  rw [exc_cat_twoPart_aux2 (a := 6 * k) (hA.mul (hB.mul hC))]
  ring

private theorem exc_cat_twoPart_aux6 {G : Type} [Group G] [Finite G] {n k : ℕ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) {i : TauCeti.CFSGIndex} (e : G ≃* i.Group) (h1 : isOmP n (2 ^ k) i) :
    padicValNat 2 (Nat.card G) = k * (n * (n - 1)) := by
  cases i with
  | cyclic pp hpp => simp [isOmP, onLie] at h1
  | alternating m hm => simp [isOmP, onLie] at h1
  | sporadic s => simp [isOmP, onLie] at h1
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | D r q =>
      change r = n ∧ q.card = 2 ^ k at h1
      obtain ⟨hr, hq⟩ := h1
      subst r
      have hcard : Nat.card G = orderD n (2 ^ k) := by
        rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.D n q, hv⟩ G ⟨e⟩]
        change orderD n q.card = orderD n (2 ^ k)
        rw [hq]
      rw [hcard, exc_cat_twoPart_aux3 hn hk]
    | _ => simp [isOmP, onLie] at h1

private theorem exc_cat_twoPart_aux7 {G : Type} [Group G] [Finite G] {n k : ℕ} (hk : 1 ≤ k)
    (hk1 : k = 1 → 5 ≤ n) (hn3 : n = 3)
    {i : TauCeti.CFSGIndex} (e : G ≃* i.Group) (h2 : isLnA 4 (2 ^ k) i) :
    padicValNat 2 (Nat.card G) = k * (n * (n - 1)) := by
  subst hn3
  rcases h2 with h2a | ⟨hm, hq, hi⟩ | ⟨hm, hq, hi⟩ | ⟨hm, hq, hi⟩ | ⟨hm, hq, hi⟩
  · cases i with
    | cyclic pp hpp => simp [onLie, isLnEps] at h2a
    | alternating m hm => simp [onLie, isLnEps] at h2a
    | sporadic s => simp [onLie, isLnEps] at h2a
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | A r q =>
        change r + 1 = 4 ∧ q.card = 2 ^ k at h2a
        obtain ⟨hr, hq⟩ := h2a
        have hr3 : r = 3 := by omega
        subst r
        have hcard : Nat.card G = orderA 3 (2 ^ k) := by
          rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.A 3 q, hv⟩ G ⟨e⟩]
          change orderA 3 q.card = orderA 3 (2 ^ k)
          rw [hq]
        rw [hcard, exc_cat_twoPart_aux5 hk]
      | _ => simp [onLie, isLnEps] at h2a
  · omega
  · omega
  · omega
  · have hk1' : k = 1 :=
      Nat.pow_right_injective (a := 2) (by norm_num) (by simpa using hq)
    have := hk1 hk1'
    omega

theorem exc_cat_twoPart {G : Type} [Group G] [Finite G] {n k : ℕ} (hn : Odd n) (hn3 : 3 ≤ n)
    (hk : 1 ≤ k) (hk1 : k = 1 → 5 ≤ n) (h : catalogIs G (isOmPA n (2 ^ k))) :
    padicValNat 2 (Nat.card G) = k * (n * (n - 1)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with h1 | ⟨hn3', h2⟩
  · exact exc_cat_twoPart_aux6 (by omega) hk e h1
  · exact exc_cat_twoPart_aux7 hk hk1 hn3' e h2


end CFSG.LocalAnalysis.GLTheoremA.I167

end
