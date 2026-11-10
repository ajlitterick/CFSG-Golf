module

public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient

public section

namespace CFSG.ClassicalInvolution.ModelFacts.ChevAut

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Chevalley

theorem exists_ringEquiv_eq_frobenius_pow {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (φ : F ≃+* F) :
    ∃ e < f, ∀ x, φ x = x ^ p ^ e := by
  obtain ⟨σ, hσ, hord, hz, -, -⟩ := finite_field_automorphism_fixed_field_cardinality hp hf hF
  have hfin : IsOfFinOrder σ := orderOf_pos_iff.1 (by rw [hord]; omega)
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1
    (hfin.mem_powers_iff_mem_zpowers.2 (by rw [hz]; exact Subgroup.mem_top φ))
  have hφ : φ = σ ^ (k % f) := by rw [← hk, ← hord, pow_mod_orderOf]
  refine ⟨k % f, Nat.mod_lt _ (by omega), fun x => ?_⟩
  rw [hφ, ringAut_pow_apply_of_frobenius hσ]


end CFSG.ClassicalInvolution.ModelFacts.ChevAut
