module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.LayerOfNotConstrained
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableNormalCyclic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Reduced
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs
open scoped commutatorElement

theorem isPSolvable_three_of_hasPrimeConstraint_of_cyclic {B : Type} [Group B] [Finite B]
    (hcyc : ∀ X : Subgroup B, IsPGroup 3 X → IsCyclic X)
    (hc : HasPrimeConstraint (G := B) 3) : CFSG.HallHigman.IsPSolvable 3 B := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hRn, hR3, hCR⟩ := hc
  obtain ⟨W, hW3, hWR⟩ :=
    CFSG.AGLEmbeddingD2.exists_isPGroup_map_mk_eq_of_isPGroup
      (primeComplementCore (G := B) 3) hR3
  haveI : IsCyclic W := hcyc W hW3
  have hRcyc : IsCyclic R := by
    rw [← hWR]
    exact isCyclic_of_surjective ((QuotientGroup.mk' (primeComplementCore (G := B) 3)).subgroupMap W)
      (MonoidHom.subgroupMap_surjective _ W)
  haveI := hRcyc
  have hsol : Group.IsSolvable (B ⧸ primeComplementCore (G := B) 3) := by
    haveI : Group.IsSolvable R := inferInstance
    apply isSolvable_of_commutatorElement_mem R
    intro a b
    have hcomm := commutator_centralizes_cyclic R (a := a⁻¹) (b := b⁻¹)
      (fun r hr => by simpa using hRn.conj_mem r hr a⁻¹)
      (fun r hr => by simpa using hRn.conj_mem r hr b⁻¹)
    apply hCR
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have := hcomm r hr
    simp only [inv_inv, commutatorElement_def]
    simpa [mul_assoc] using this.symm
  exact isPSolvable_of_normal_coprime_quotient_solvable (primeComplementCore (G := B) 3)
    (primeComplementCore_coprime 3) hsol

theorem isPSolvable_three_of_coprime {K : Type} [Group K] [Finite K]
    (h : Nat.Coprime 3 (Nat.card K)) : CFSG.HallHigman.IsPSolvable 3 K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine isPSolvable_of_normal_coprime_quotient_solvable (⊤ : Subgroup K) ?_ ?_
  · rwa [Subgroup.card_top]
  · haveI : Subsingleton (K ⧸ (⊤ : Subgroup K)) := QuotientGroup.subsingleton_quotient_top
    infer_instance


end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
