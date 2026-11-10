module

public import CFSG.CGT.Stroth77.StrothAmbient
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.CGT.Stroth77

variable {G : Type*} [Group G] [Finite G] {X : StrothAmbient G}

theorem StrothTypeIndex.m_eq_n_or_succ_or_succ_succ (τ : StrothTypeIndex) :
    τ.m + 1 = τ.n ∨ τ.m + 2 = τ.n ∨ τ.m = τ.n := by
  cases τ <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)


end CFSG.CGT.Stroth77
