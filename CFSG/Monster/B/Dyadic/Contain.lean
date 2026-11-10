module

public import CFSG.Monster.B.Dyadic.Elim
public import Certificates.Certificate3102

public section

namespace CFSG.Monster.B.Dyadic

open CFSG.Monster.B.Dyadic.Native


structure BasisFacts : Prop where
  pexp_le : ∀ i < 4371, diagExpK[i]! ≤ 7
  diag : ∀ i < 4371, (basisRowsK[i]!.get! i).toNat = 2 ^ diagExpK[i]!
  lower : ∀ i < 4371, ∀ k < i, basisRowsK[i]!.get! k = 0
  upper : ∀ i < 4371, ∀ k < 4371, i < k → (basisRowsK[i]!.get! k).toNat < 128

theorem basis_facts : BasisFacts := by
  obtain ⟨h1, h2, h3, h4, -⟩ := Certificates.certificate3102
  refine ⟨fun i hi => h1 ⟨i, hi⟩, fun i hi => ?_, fun i hi k hk => ?_, fun i hi k hk hik => ?_⟩
  · have := h2 ⟨i, hi⟩
    rw [Bz] at this
    exact_mod_cast this
  · have := h3 ⟨i, hi⟩ ⟨k, by omega⟩ hk
    rw [Bz] at this
    have e : (basisRowsK[i]!.get! k).toNat = 0 := by exact_mod_cast this
    exact UInt8.toNat_inj.1 (e.trans UInt8.toNat_zero.symm)
  · have := h4 ⟨i, hi⟩ ⟨k, hk⟩ hik
    rw [Bz] at this
    exact_mod_cast this


end CFSG.Monster.B.Dyadic

end
