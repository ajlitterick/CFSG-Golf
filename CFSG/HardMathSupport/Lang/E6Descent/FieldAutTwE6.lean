module

public import CFSG.HardMathSupport.Lang.E6Descent.OutRankTwE6
public import CFSG.HardMathSupport.Lang.E6Descent.FixedTwE6
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6Noninner

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.Chevalley


section Main

theorem exists_conj_fieldActor_twE6 {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hp : p.Prime) (hp3 : 3 < p)
    (α : MulAut (twistedE6RootGroup K σ)) (hα : IsOuterOfOrder p α) :
    ∃ (ψ : MulAut (twistedE6RootGroup K σ)) (η : K ≃+* K), orderOf η = p ∧
      ψ * α * ψ⁻¹ = fieldActor σ η := by
  classical
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨hord, hout⟩ := hα
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  let α' : (⊤ : Subgroup (MulAut (twistedE6RootGroup K σ))) := ⟨α, Subgroup.mem_top _⟩
  have hα' : (α' : MulAut (twistedE6RootGroup K σ)) ∉
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range :=
    fun ⟨g, hg⟩ => hout g hg.symm
  have hαp : orderOf α' = p := by rw [Subgroup.orderOf_mk]; exact hord
  obtain ⟨hηo, -, ⟨ψ, hψ⟩, -⟩ :=
    twisted_E6_noninner_large_prime_field_descent_and_local_core_trivial hℓ hf K hK' σ hσ Θ hΘ hp
      hp3 ⊤ le_top α' hα' hαp
  exact ⟨ψ, Θ α', hηo, hψ⟩


end Main

end CFSG.HardMathSupport.Lang.E6Descent
