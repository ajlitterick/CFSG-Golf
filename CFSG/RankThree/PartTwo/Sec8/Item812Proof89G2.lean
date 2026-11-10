module

public import CFSG.RankThree.PartTwo.Sec8.Item812Proof89
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
import CFSG.RankThree.PartTwo.KFacts.K71G2
import CFSG.RankThree.PartTwo.KFacts.K71Item89
import CFSG.LieType.Chevalley.EvenRootCommutatorF4

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint.Chevalley


theorem kF89GTwo : KF89GTwo := by
  intro G _ _ X a q hp hG ha3 hout
  obtain ⟨hv, ⟨e₀⟩⟩ := hG
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := GaloisField 2 q.exponent
  have hK : Nat.card K = q.card := by
    rw [GaloisField.card 2 q.exponent q.exponent_pos.ne', TauCeti.PrimePower.card_def, hp]
  have hq3 : 3 ≤ q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK, TauCeti.PrimePower.card_def, hp] at *
    rcases Nat.lt_or_ge q.exponent 2 with h2 | h2
    · interval_cases h : q.exponent <;> simp_all
    · exact (Nat.pow_le_pow_right (by norm_num) h2 : 2 ^ 2 ≤ 2 ^ q.exponent)
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hp K hK
  set e : X ⧸ aschbacherSolvableCore 3 X ≃* adjointGroup Tag.G2 K :=
    (e₀.trans b.symm).trans ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := Tag.G2) (K := K))).trans
      QuotientGroup.quotientBot)
  have hchar : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨-, σ, -, hcard, ⟨ι⟩⟩ := KFacts.exists_barCentralizer_mulEquiv_g2 hchar hK4 ha3 hout e
  have hdvd : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) ∣ 2 ^ q.exponent := by
    have h1 := dvd_pow_self (Nat.card (CFSG.LieType.Chevalley.fixSubfield σ))
      (by norm_num : (3 : ℕ) ≠ 0)
    rwa [hcard, hK, TauCeti.PrimePower.card_def, hp] at h1
  obtain ⟨r, -, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact KFacts.not_nonempty_perfectResidual_mulEquiv_alternatingGroup_six_of_isoGTwoEven
    ⟨_, inferInstance, inferInstance, hr, ⟨ι⟩⟩

end CFSG.RankThree.PartTwo.Sec8
