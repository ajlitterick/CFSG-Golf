module

public import CFSG.Quasithin.Background.VolIE54
public import CFSG.Quasithin.Background.GoldschmidtE5TwoStab
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.RonanE51

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_forall_pow_mem {Y : Type*} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]
    (hN : Group.IsSolvable ↥N) (h : ∀ y : Y, ∃ k : ℕ, y ^ 2 ^ k ∈ N) : Group.IsSolvable Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : IsPGroup 2 (Y ⧸ N) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h y
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
  have : Group.IsSolvable (Y ⧸ N) := by
    have := hq.isNilpotent
    infer_instance
  exact Group.isSolvable_of_subgroup_quotient N


end CFSG.Quasithin.RonanE51
