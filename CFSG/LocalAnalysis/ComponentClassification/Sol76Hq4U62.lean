module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4L34
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Quot
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.DSFactsModel
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.LiftedSchreierData
public import CFSG.ClassicalGroups
public import CFSG.Foundations
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Statements
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LieType.Steinberg.CentralExt.GriessTable
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Table
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13CenterTwo
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Functor
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut
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
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Presentation.Suz
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
open CFSG.LieType.Steinberg.CentralExt

theorem card_dvd_card_centralizer_of_conj_mem {S : Type*} [Group S] [Finite S] {A : Subgroup S}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {x g : S} (hg : g * x * g⁻¹ ∈ A) :
    Nat.card A ∣ Nat.card (centralizer ({x} : Set S)) := by
  rw [card_centralizer_mulEquiv (MulAut.conj g) x]
  refine Subgroup.card_dvd_of_le fun a ha => ?_
  rw [mem_centralizer_singleton_iff]
  exact hA a ha _ hg

theorem pow_nine_dvd_card_centralizer_of_U62
    {S : Type} [Group S]
    (hL : LieModel S .PSU 6 2 1) {x : S} (hx : orderOf x = 2) :
    2 ^ 9 ∣ Nat.card (centralizer ({x} : Set S)) := by
  obtain ⟨D⟩ := EvenSmallLie.UnitarySix.nonempty_toddParabolic hL
  have := D.finite
  obtain ⟨g, hg⟩ := D.conj_into_A x hx
  rw [← D.card_A]
  exact card_dvd_card_centralizer_of_conj_mem D.A_comm hg

theorem centralFour_U62
    {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q) (hL : LieModel (Q ⧸ center Q) .PSU 6 2 1)
    {u v : Q} (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u ≠ v) (huZ : u ∈ center Q)
    (hvZ : v ∈ center Q) :
    (∃ x : Q, orderOf x = 2 ∧ x ∉ center Q) ∧
      ∀ x : Q, orderOf x = 2 → x ∉ center Q →
        (Nat.card ↥(center Q)).factorization 2 + 2 ≤
          (Nat.card ↥(centralizer ({x} : Set Q))).factorization 2 := by
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have hv2 : v * v = 1 := by rw [← pow_two, ← hv, pow_orderOf_eq_one]
  have hu1 : u ≠ 1 := by rintro rfl; rw [orderOf_one] at hu; omega
  have hv1 : v ≠ 1 := by rintro rfl; rw [orderOf_one] at hv; omega
  have hrow : GriessAll.GriessRow (Q ⧸ center Q) .PSU 6 2 1 :=
    GriessClassical.psu_six_two_row (GriessNative.models_lieModel_of_classical
      (GriessNative.classical_of_lieModel hL (by decide)))
  have hodd : (¬ 2 ∣ (genericOrders .PSU 6 2 1).1 ∧ ¬ 2 ∣ (genericOrders .PSU 6 2 1).2) ∨
      (¬ 2 ∣ (exceptionalOrders .PSU 6 2 1).1 ∧ ¬ 2 ∣ (exceptionalOrders .PSU 6 2 1).2) :=
    Or.inl (by decide)
  refine ⟨?_, fun x hx hxZ => ?_⟩
  ·
    obtain ⟨N, _, -, hN2, hQN, h2, ⟨e'⟩, -⟩ :=
      exists_twoCover_quotient hQ huZ hvZ hu2 hv2 hu1 hv1 huv
    have : Group.IsPerfect (Q ⧸ N) := hQN.1
    have hL' : LieModel ((Q ⧸ N) ⧸ center (Q ⧸ N)) .PSU 6 2 1 :=
      GSThmB.OddQuot.lieModel_of_equiv e'.symm hL
    obtain ⟨M, hZM, hM2, hMcard⟩ := EvenSmallLie.UnitarySix.exists_elementary_preimage h2 hL'
    have hne : ∃ y ∈ M, y ∉ center (Q ⧸ N) := by
      by_contra hcon
      push Not at hcon
      have hbot : M.map (QuotientGroup.mk' (center (Q ⧸ N))) = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨y, hy, rfl⟩
        rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hcon y hy
      rw [hbot, Subgroup.card_bot] at hMcard
      norm_num at hMcard
    obtain ⟨y, hyM, hyZ⟩ := hne
    exact exists_noncentral_involution_of_quotient hN2
      (by rw [← pow_two]; exact hM2 y hyM) hyZ
  ·
    have hx2 : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
    refine clause_two_of_griessRow hQ hrow hodd huZ hvZ hu2 hv2 hu1 hv1 huv hx2 ?_
    have hxb : orderOf (x : Q ⧸ center Q) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two, ← QuotientGroup.mk_mul, hx2]; rfl
      · intro h
        exact hxZ ((QuotientGroup.eq_one_iff x).mp h)
    have h9 := pow_nine_dvd_card_centralizer_of_U62 hL hxb
    have := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h9
    omega

end CFSG.ComponentClassification.Sol76T13.Hq4
