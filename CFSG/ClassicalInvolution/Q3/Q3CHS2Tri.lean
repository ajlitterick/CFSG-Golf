module

public import CFSG.ClassicalInvolution.Q3.Q3TAxis
public import CFSG.ClassicalInvolution.Q3.Q3YQuat
public import CFSG.ClassicalInvolution.Q3.Q3ABoot

public section

namespace CFSG.ClassicalInvolution.Q3.Q3CH

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]


theorem mem_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    {x : G} (hx : x ∈ Subgroup.closure ({a, b} : Set G)) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b :=
  CFSG.ClassicalInvolution.Q3.mem_closure_pair_cases ha hb hab hx

theorem isPGroup_sup_of_commute {A B : Subgroup G} (hA : IsPGroup 2 A) (hB : IsPGroup 2 B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : IsPGroup 2 ↥(A ⊔ B) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  hA.to_sup_of_normal_right' hB fun a ha =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (hAB a ha b hb).symm)

end CFSG.ClassicalInvolution.Q3.Q3CH
