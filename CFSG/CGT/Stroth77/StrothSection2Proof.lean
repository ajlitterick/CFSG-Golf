module

public import CFSG.CGT.Stroth77.StrothAmbient
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.CGT.Stroth77

variable {G : Type*} [Group G] [Finite G] {X : StrothAmbient G}

theorem StrothTypeIndex.m_eq_n_or_succ_or_succ_succ (τ : StrothTypeIndex) :
    τ.m + 1 = τ.n ∨ τ.m + 2 = τ.n ∨ τ.m = τ.n := by
  cases τ <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)


theorem item224_involutions_of_A_le_mho (Z : StrothDatum X)
    (hA : X.A ≤ mhoOne Z.D) :
    ∀ z : G, z ∈ Z.centralizerInMho → z * z = 1 → z ∈ omegaIn 1 Z.D := by
  intro z hz hz2
  have hzS : z ∈ (X.S : Subgroup G) := hz.1.1
  have hzCentA : z ∈ Subgroup.centralizer (X.A : Set G) :=
    Subgroup.centralizer_le (show (X.A : Set G) ⊆ (mhoOne Z.D : Set G) from hA) hz.2
  have hzA : z ∈ X.A := X.hH z hzS hz2 hzCentA
  have hzD : z ∈ Z.D := Z.hAD hzA
  refine ⟨⟨z, hzD⟩, Subgroup.subset_closure ?_, rfl⟩
  change (⟨z, hzD⟩ : Z.D) ^ (2 ^ 1) = 1
  apply Subtype.ext
  simpa [pow_two] using hz2


end CFSG.CGT.Stroth77
