module

public import CFSG.RankThree.GF2n.Smith81.Sec1Fusion

public section

namespace CFSG.RankThree.GF2n.Smith81

section LinearAlgebra

open Matrix

section RankOneTransvection

variable {K : Type*} [Field K] {n : ℕ}

theorem exists_dotProduct_row {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → K) →ₗ[K] K) :
    ∃ γ : ι → K, ∀ x, f x = γ ⬝ᵥ x := by
  refine ⟨fun i => f (fun j => if i = j then 1 else 0), fun x => ?_⟩
  rw [LinearMap.pi_apply_eq_sum_univ f x]
  simp only [dotProduct, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem exists_dotProduct_one {r : Fin n → K} (hr : r ≠ 0) : ∃ x : Fin n → K, r ⬝ᵥ x = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
    by_contra h
    push Not at h
    exact hr (funext h)
  exact ⟨(r i)⁻¹ • Pi.single i 1, by simp [dotProduct_smul, Pi.single_apply, hi]⟩

theorem vecMulVec_mulVec_smul (p r x : Fin n → K) : vecMulVec p r *ᵥ x = (r ⬝ᵥ x) • p := by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm]

end RankOneTransvection

end LinearAlgebra

section CosetLift

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]


end CosetLift

section Assembly

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise Matrix
open CFSG.Open.StatedAPI
open CFSG.RankThree.GF2n.Stroth80

theorem exists_sit_of_isConj {G : Type} [Group G] {M Q Z : Subgroup G}
    (Hs : StrothHyp M Q Z) {z x : G} (hz : z ∈ Z) (hx : IsConj z x) (hxM : x ∈ M)
    (hxQ : x ∉ Q) :
    ∃ X : Subgroup G, Sit M Q Z X x := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hx
  refine ⟨conjSubgroup c Z, Hs, ⟨c, rfl⟩, ?_, ?_, hxM, hxQ⟩
  · rw [mem_conjSubgroup]
    have e : c⁻¹ * x * c = z := by rw [← hc]; group
    rw [e]
    exact hz
  · intro h1
    apply hxQ
    rw [h1]
    exact Subgroup.one_mem Q

theorem charP_two_of_natCard_pow_two {K : Type} [Field K] [Finite K] {k : ℕ}
    (hk : Nat.card K = 2 ^ k) : CharP K 2 := by
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hp, hm⟩ := FiniteField.card K (ringChar K)
  rw [← Nat.card_eq_fintype_card, hk] at hm
  have h1 : ringChar K ∣ 2 ^ k := by
    rw [hm]
    exact dvd_pow_self _ (PNat.ne_zero m)
  have h2 : ringChar K ∣ 2 := hp.dvd_of_dvd_pow h1
  have h3 : ringChar K = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  rw [← h3]
  exact ringChar.charP K

end Assembly

end CFSG.RankThree.GF2n.Smith81
