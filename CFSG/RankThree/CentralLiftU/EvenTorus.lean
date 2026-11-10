module

public import CFSG.RankThree.CentralLiftU.UnitaryLiftGen
public import CFSG.RankThree.CentralLiftU.UnitaryTorusWeylOdd
public import CFSG.RankThree.CentralLiftU.UnitaryThreeEven

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.CentralLift (IsLargeCentralExt)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (IsLinePerm)

namespace Gen

section TorusGen

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {r : ℕ}

section Torus

variable {R : Type*} [Group R] {π : R →* hypSU h r 1} (hS : LiftHyp h π)
  {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
include hS


end Torus

end TorusGen

section Even

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {r ε : ℕ}

include h in
theorem charP_two : CharP K 2 := h.charP


theorem odd_card_ker {R : Type*} [Group R] [Finite R] {G : Type*} [Group G] {π : R →* G}
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpk : IsPGroup p π.ker) : Odd (Nat.card π.ker) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hpk.exists_card_eq
  rw [hn]
  exact (hp.odd_of_ne_two (by omega)).pow


end Even

end Gen

end CFSG.RankThree.CentralLiftU
