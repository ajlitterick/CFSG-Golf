module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3Sound
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3Cover
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.Blueprint
  CFSG.CosetTable CFSG.Sporadic.Recognition.CoverRecipe CFSG.AGLEmbedding

theorem factorization_three_pow_mul (k b : Nat) (hb : ¬ 3 ∣ b) (hb0 : b ≠ 0) :
    (3 ^ k * b).factorization 3 = k := by
  rw [Nat.factorization_mul (by positivity) hb0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hb, add_zero]

theorem factorization_three_le {N n k b c : Nat} (hN : N = 3 ^ k * b) (hn : n = 3 ^ k * c)
    (hb : ¬ 3 ∣ b) (hb0 : b ≠ 0) (hc : ¬ 3 ∣ c) (hc0 : c ≠ 0) :
    N.factorization 3 ≤ n.factorization 3 := by
  rw [hN, hn, factorization_three_pow_mul k b hb hb0, factorization_three_pow_mul k c hc hc0]


end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
