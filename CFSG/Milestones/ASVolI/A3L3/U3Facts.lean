module

public import CFSG.Milestones.ASVolI.A3L3.U3Data
public import CFSG.Milestones.ASVolI.A3L3.Finish
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA

public section

namespace CFSG.ASVolI

open Matrix CFSG.RankThree.SubgroupLists CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts

variable {p : ℕ} {K : Type} [Field K]


section Model

variable (hU : UnitaryFieldData p 1 K) [Finite K] (two_ne : (2 : K) ≠ 0) {x y cc : K}
  (hdet : cc ^ 2 * (x ^ 2 + y ^ 2) = -1) (hx : hU.bar x = x) (hy : hU.bar y = y)
  (hc : hU.bar cc = -cc)

local notation "MU" => burnsideA315y_u3Model hU two_ne hdet hx hy hc


end Model


section Model2

variable (hU : UnitaryFieldData p 1 K) [Finite K] (two_ne : (2 : K) ≠ 0) {x y cc : K}
  (hdet : cc ^ 2 * (x ^ 2 + y ^ 2) = -1) (hx : hU.bar x = x) (hy : hU.bar y = y)
  (hc : hU.bar cc = -cc)

local notation "MU" => burnsideA315y_u3Model hU two_ne hdet hx hy hc


theorem burnsideA315y_u3_hoddc :
    ∀ φ : MulAut (unitaryPSU hU 3), Odd (orderOf φ) → φ ∈ (MU).c.range := by
  intro φ hodd
  have hp := hU.prime
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · exfalso
      have hp2 : p = 2 := by omega
      subst hp2
      have : (2 : K) = 0 := by
        have : CharP K 2 := hU.charP
        exact_mod_cast CharP.cast_eq_zero K 2
      exact two_ne this
    · exact h
  have hq : 2 < p ^ 1 := by rw [pow_one]; omega
  obtain ⟨A, σ, hφ⟩ := exists_psuConj_mul_psuField hq φ
  have hcard : Nat.card K = p ^ 2 := by rw [hU.card]
  have hσ2 : σ ^ 2 = 1 := by
    have h2 := (card_ringAut_and_isCyclic hp K hcard).1
    rw [← h2]
    exact pow_card_eq_one'
  have hσσ : psuField hU σ * psuField hU σ = 1 := by rw [← map_mul, ← sq, hσ2, map_one]
  have hσinv : (psuField hU σ)⁻¹ = psuField hU σ := inv_eq_of_mul_eq_one_right hσσ
  have hsq : φ ^ 2 ∈ (psuConj hU).range := by
    refine ⟨A * ⟨CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut σ A,
      glAut_mem_unitaryIsom3 σ A.2⟩, ?_⟩
    rw [map_mul, ← psuField_mul_psuConj_mul_inv σ A, hσinv, hφ, sq]
    simp only [mul_assoc]
  obtain ⟨k, hk⟩ := hodd
  have hφk : φ = (φ ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf φ + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [hφk]
  exact Subgroup.pow_mem _ hsq _


end Model2

end CFSG.ASVolI
