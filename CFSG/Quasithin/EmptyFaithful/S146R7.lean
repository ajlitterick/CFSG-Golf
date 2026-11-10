module

public import CFSG.Quasithin.EmptyFaithful.S146R6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G]

theorem exists_odd_of_secIso_dihedral {A Q : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : SecIso A Q (DihedralGroup p)) : ∃ z ∈ A, z ∉ Q ∧ Odd (orderOf z) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨hQn, ⟨e⟩⟩ := h
  have hord : orderOf (e.symm (DihedralGroup.r 1)) = p := by
    rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm (DihedralGroup.r 1))
  obtain ⟨k, hk⟩ := exists_odd_orderOf_pow (y : G)
  have hzA : (y : G) ^ 2 ^ k ∈ A := A.pow_mem y.2 _
  refine ⟨(y : G) ^ 2 ^ k, hzA, fun hzQ => ?_, hk⟩
  have hone : (QuotientGroup.mk (⟨(y : G) ^ 2 ^ k, hzA⟩ : ↥A) : ↥A ⧸ Q.subgroupOf A) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hzQ)
  have hpow : (e.symm (DihedralGroup.r 1)) ^ 2 ^ k = 1 := by
    rw [← hy, ← QuotientGroup.mk_pow]
    exact hone
  have hdvd : p ∣ 2 ^ k := hord ▸ orderOf_dvd_of_pow_eq_one hpow
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))


end CFSG.Quasithin
