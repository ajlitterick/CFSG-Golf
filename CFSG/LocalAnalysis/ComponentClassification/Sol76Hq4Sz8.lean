module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4L34
public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks
public import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers
public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.Certificates.LiftedSchreierData
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LieType.Steinberg.CentralExt.GriessTable
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Table
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13CenterTwo
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Functor
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.Sporadic.Bridge.BOrder
public import CFSG.Sporadic.Bridge.BSurjInputs
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import CFSG.Sporadic.Fi24.Simple
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.PrimitiveBase
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.Schreier.RuLOdd
public import CFSG.Sporadic.Schreier.RuZClass
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.ThSchreier.GlobalIndexBase
public import CFSG.Walter.JRFacts
public import CFSG.Walter.W67.Statements

public section

namespace CFSG.ComponentClassification.Sol76T13.Hq4

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier
open CFSG.LieType.Steinberg.CentralExt CFSG.RankThree.PartTwo.Sec4.Census

theorem four_le_factorization_centralizer_of_Sz8 {S : Type}
    [Group S] {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8) (e : S ≃* suzukiGroup 1 K)
    {x : S} (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    4 ≤ (Nat.card (centralizer ({x} : Set S))).factorization 2 := by
  have hK' : Nat.card K = 2 ^ (2 * 1 + 1) := by rw [hK]; norm_num
  have := CFSG.LieType.Ree.finite_suzukiGroup hK'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : orderOf (e x) = 2 :=
    orderOf_eq_prime (by rw [pow_two, ← map_mul, hx2, map_one])
      (fun h => hx1 (e.injective (by rw [h, map_one])))
  have hzp : IsPGroup 2 (zpowers (e x)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  have hC := RankThree.centralizer_eq_sylow hK' hz P (hP (mem_zpowers _))
  rw [card_centralizer_mulEquiv e, hC, Sylow.card_eq_multiplicity,
    RankThree.PartTwo.KFacts.KP7.card_suzukiGroup_eight hK,
    Nat.Prime.factorization_pow Nat.prime_two]
  have h29 : (29120 : ℕ).factorization 2 = 6 := by
    rw [show (29120 : ℕ) = 2 ^ 6 * 455 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 455)]
    simp
  simp [h29]

noncomputable def tauCetiSz8Equiv {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8) :
    TauCeti.suzukiGroup 1 ≃* suzukiGroup 1 K :=
  (BenderSuzuki.Catalog.suzukiGroupEquiv 1).trans
    (ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup
      (a := 1) (K := K) (by rw [hK]; norm_num)).symm

theorem exists_noncentral_involution_of_Sz8 {Q : Type} [Group Q] [Finite Q] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 8) (e : Q ⧸ center Q ≃* suzukiGroup 1 K) :
    ∃ x : Q, orderOf x = 2 ∧ x ∉ center Q := by
  let f : TauCeti.suzukiGroup 1 →* Q ⧸ center Q :=
    ((tauCetiSz8Equiv hK).trans e.symm).toMonoidHom
  have hD := DoubleCoverRanks.sz8_e8Datum.map f ((tauCetiSz8Equiv hK).trans e.symm).injective
  let φ := QuotientGroup.mk' (center Q)
  obtain ⟨b₁, -, -, hb₁, -, -, hb₁2, -⟩ :=
    hD.exists_lift (φ := φ) (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
  have hb₁1 : φ b₁ ≠ 1 := by rw [hb₁]; exact hD.ne_one
  refine ⟨b₁, orderOf_eq_prime hb₁2 (fun h => hb₁1 (by rw [h, map_one])), fun h => hb₁1 ?_⟩
  exact (QuotientGroup.eq_one_iff b₁).mpr h

theorem centralFour_Sz8
    {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    (hL : LieModel (Q ⧸ center Q) .twistedB2 0 2 3) {u v : Q} (hu : orderOf u = 2)
    (hv : orderOf v = 2) (huv : u ≠ v) (huZ : u ∈ center Q) (hvZ : v ∈ center Q) :
    (∃ x : Q, orderOf x = 2 ∧ x ∉ center Q) ∧
      ∀ x : Q, orderOf x = 2 → x ∉ center Q →
        (Nat.card ↥(center Q)).factorization 2 + 2 ≤
          (Nat.card ↥(centralizer ({x} : Set Q))).factorization 2 := by
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have hv2 : v * v = 1 := by rw [← pow_two, ← hv, pow_orderOf_eq_one]
  have hu1 : u ≠ 1 := by rintro rfl; rw [orderOf_one] at hu; omega
  have hv1 : v ≠ 1 := by rintro rfl; rw [orderOf_one] at hv; omega
  obtain ⟨-, -, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := GriessNative.suzuki_of_lieModel hL
  obtain rfl : a = 1 := by omega
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  have hrow := GriessNative.twistedB2_row hL
  have hodd : (¬ 2 ∣ (genericOrders .twistedB2 0 2 3).1 ∧
      ¬ 2 ∣ (genericOrders .twistedB2 0 2 3).2) ∨
      (¬ 2 ∣ (exceptionalOrders .twistedB2 0 2 3).1 ∧
        ¬ 2 ∣ (exceptionalOrders .twistedB2 0 2 3).2) :=
    Or.inl (by decide)
  refine ⟨exists_noncentral_involution_of_Sz8 hK8 e, fun x hx hxZ => ?_⟩
  have hx2 : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  refine clause_two_of_griessRow hQ hrow hodd huZ hvZ hu2 hv2 hu1 hv1 huv hx2 ?_
  refine four_le_factorization_centralizer_of_Sz8 hK8 e ?_ ?_
  · rw [← QuotientGroup.mk_mul, hx2]; rfl
  · intro h
    exact hxZ ((QuotientGroup.eq_one_iff x).mp h)

end CFSG.ComponentClassification.Sol76T13.Hq4
