module

public import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
public import CFSG.Quasithin.EmptyFaithful.T1531InspMod
public import CFSG.Quasithin.EmptyFaithful.T1531Cat

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem perm_fin3_sign_eq_one_of_odd {σ : Equiv.Perm (Fin 3)} (h : Odd (orderOf σ)) :
    Equiv.Perm.sign σ = 1 := by
  obtain ⟨k, hk⟩ := h
  have h1 : Equiv.Perm.sign σ ^ orderOf σ = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rw [hk, pow_succ, pow_mul, Int.units_sq, one_pow, one_mul] at h1
  exact h1

theorem perm_fin3_eq_pow_of_sign_eq_one :
    ∀ σ τ : Equiv.Perm (Fin 3), Equiv.Perm.sign σ = 1 → Equiv.Perm.sign τ = 1 → τ ≠ 1 →
      σ = 1 ∨ σ = τ ∨ σ = τ ^ 2 := by
  decide +kernel

section S3

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

omit [Finite G] in
theorem oTwoUpper_G2_153 (r67 : Res15367 T Mc M V₁ V₂ E) (hT2 : IsPGroup 2 ↥(TE153 T E)) :
    oTwoUpper (G2_153 T E) = XE153 E :=
  oTwoUpper_sup_eq (oTwoUpper_oTwoUpper _).symm hT2 (inf_le_right.trans r67.XE_normal)


end S3

section Top


end Top

end CFSG.Quasithin
