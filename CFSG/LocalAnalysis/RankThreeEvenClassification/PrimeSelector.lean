module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalRank

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

def aschbacherStratumOne (G : Type u) [Group G] [Finite G] : Set ℕ :=
  {prime | prime.Prime ∧ prime ≠ 2 ∧ prime ∣ Nat.card G ∧ 3 < twoLocalRank prime G}

def aschbacherStratumTwo (G : Type u) [Group G] [Finite G] : Set ℕ :=
  {prime | prime.Prime ∧ 5 < prime ∧ prime ∣ Nat.card G ∧ twoLocalRank prime G = 3}

def aschbacherStratumThree (G : Type u) [Group G] [Finite G] : Set ℕ :=
  {prime | prime.Prime ∧ 3 < prime ∧ prime ∣ Nat.card G ∧ twoLocalRank prime G = 3}

def aschbacherStratumFour (G : Type u) [Group G] [Finite G] : Set ℕ :=
  {prime | prime.Prime ∧ prime ≠ 2 ∧ prime ∣ Nat.card G ∧ twoLocalRank prime G = 3}

@[expose] noncomputable def aschbacherPrimes (G : Type u) [Group G] [Finite G] : Set ℕ := by
  classical
  exact if (aschbacherStratumOne G).Nonempty then aschbacherStratumOne G
    else if (aschbacherStratumTwo G).Nonempty then aschbacherStratumTwo G
    else if (aschbacherStratumThree G).Nonempty then aschbacherStratumThree G
    else if (aschbacherStratumFour G).Nonempty then aschbacherStratumFour G else ∅


end CFSG.RankThreeEvenClassification.Helpers
