module

public import CFSG.RankThree.PartOne.Census3.Interface
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeBEven
public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeDEven
public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeTD
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessBThree
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessDTheta
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessTDFour

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti


theorem le_localRank_of_hasWitness' {d : ValidLieTypeIndex} {p k : ℕ} (hp : p.Prime)
    (h : HasWitness d.Group p k) [hfin : Finite (CFSGIndex.lie d).Group] :
    k ≤ localRank p (CFSGIndex.lie d).Group := by
  have : Finite d.Group := hfin
  exact le_localRank_of_hasWitness hp h


theorem le_localRank_B {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.B r q).Valid) {p k : ℕ}
    (hp : p.Prime) (h : HasWitness (TypeBLieIndex.Group ⟨⟨.B r q, hv⟩, trivial⟩) p k)
    [Finite (CFSGIndex.lie ⟨.B r q, hv⟩).Group] :
    k ≤ localRank p (CFSGIndex.lie ⟨.B r q, hv⟩).Group :=
  le_localRank_of_hasWitness' (d := ⟨.B r q, hv⟩) hp h

theorem le_localRank_twistedD {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.twistedD r q).Valid)
    {p k : ℕ} (hp : p.Prime)
    (h : HasWitness (TypeTwistedDLieIndex.Group ⟨⟨.twistedD r q, hv⟩, by simp⟩) p k)
    [Finite (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group] :
    k ≤ localRank p (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group :=
  le_localRank_of_hasWitness' (d := ⟨.twistedD r q, hv⟩) hp h

theorem spinLarge_typeB3 (q : PrimePower) (hv : (LieTypeIndex.B 3 q).Valid) (hp : q.p = 2)
    (hf : 3 ≤ q.exponent) [Finite (CFSGIndex.lie ⟨.B 3 q, hv⟩).Group] :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧ 3 ≤ localRank r (CFSGIndex.lie ⟨.B 3 q, hv⟩).Group := by
  obtain ⟨hchar, hord, -, hrank⟩ := typeB_mk_data 3 q hv
  rw [hp] at hchar hord
  have hq4 : 4 ≤ (⟨⟨.B 3 q, hv⟩, trivial⟩ : TypeBLieIndex).1.fieldOrder := by
    rw [hord]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨s, hs, hs5, hsd⟩ := exists_prime_five_le_dvd_two_pow_sub_one hf
  refine ⟨s, hs, by omega, le_trans (le_of_eq ?_) (le_localRank_B hv hs
    (CarrierB.hasWitness_torus _ hchar hq4 hs (hord ▸ hsd) id id
      (CarrierB.det_full_ne_zero _ (by omega) hs (by omega))))⟩
  rw [Fintype.card_fin, hrank]

theorem spinLarge_twistedD4 (q : PrimePower) (hv : (LieTypeIndex.twistedD 4 q).Valid)
    (hp : q.p = 2) (hf : 2 ≤ q.exponent) [Finite (CFSGIndex.lie ⟨.twistedD 4 q, hv⟩).Group] :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧ 3 ≤ localRank r (CFSGIndex.lie ⟨.twistedD 4 q, hv⟩).Group := by
  obtain ⟨hchar, hord, hexp, hrank⟩ := typeTwistedD_mk_data 4 q hv
  by_cases hf2 : q.exponent = 2
  · exact ⟨5, Nat.prime_five, by norm_num, le_localRank_twistedD hv Nat.prime_five
      (CarrierTD.hasWitness_tdfour _ (hchar.trans hp) (hexp.trans hf2))⟩
  rw [hp] at hchar hord
  have hq4 : 4 ≤ (⟨⟨.twistedD 4 q, hv⟩, by simp⟩ : TypeTwistedDLieIndex).1.fieldOrder := by
    rw [hord]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨s, hs, hs5, hsd⟩ := exists_prime_five_le_dvd_two_pow_sub_one (show 3 ≤ q.exponent by
    omega)
  exact ⟨s, hs, by omega, le_localRank_twistedD hv hs
    (CarrierTD.hasWitness_torus_four _ hchar hq4 hs (by omega) (hord ▸ hsd) hrank)⟩

end CFSG.RankThree.PartTwo.Census.Spin
