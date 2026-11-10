module

public import CFSG.LocalAnalysis.SectionRank.QTK.List
public import CFSG.LocalAnalysis.SectionRank.QTK.OddBasic
public import CFSG.LocalAnalysis.SectionRank.QTK.OddTorusU
import CFSG.RankThree.PartOne.Census3.LinearWitness
import CFSG.RankThree.PartTwo.Census.OddClassical.LinearWitness
import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryWitness
import CFSG.RankThree.PartTwo.Census.OddClassical.SymplecticWitness
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.SectionRank.QTK

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem not_dvd_four_of_odd_prime {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : ¬ r ∣ 4 := fun h4 =>
  hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
    (hr.dvd_of_dvd_pow (show r ∣ 2 ^ 2 by simpa using h4)))


end CFSG.SectionRank.QTK
