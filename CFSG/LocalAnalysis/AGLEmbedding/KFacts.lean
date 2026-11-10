module

public import CFSG.Open.Defs
public import CFSG.Open.GeneratedCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

section Aut

variable (p : ℕ) (K : Type) [Group K]

@[expose] def KOutRankLeOne : Prop :=
  ∀ F : Subgroup (MulAut K), IsElemAbelian p F →
    F ⊓ (MulAut.conj : K →* MulAut K).range = ⊥ → Nat.card F ≤ p

@[expose] def KSylowTI : Prop :=
  ∀ U V : Sylow p K, (U : Subgroup K) ⊓ (V : Subgroup K) ≠ ⊥ → U = V

@[expose] def KBorelMetabelian : Prop :=
  ∀ U : Sylow p K,
    ⁅⁅Subgroup.normalizer (((U : Subgroup K).map (MulAut.conj : K →* MulAut K) :
          Subgroup (MulAut K)) : Set (MulAut K)),
        Subgroup.normalizer (((U : Subgroup K).map (MulAut.conj : K →* MulAut K) :
          Subgroup (MulAut K)) : Set (MulAut K))⁆,
      ⁅Subgroup.normalizer (((U : Subgroup K).map (MulAut.conj : K →* MulAut K) :
          Subgroup (MulAut K)) : Set (MulAut K)),
        Subgroup.normalizer (((U : Subgroup K).map (MulAut.conj : K →* MulAut K) :
          Subgroup (MulAut K)) : Set (MulAut K))⁆⁆ ≤
      (U : Subgroup K).map (MulAut.conj : K →* MulAut K)

@[expose] def RankOneLieAutFacts : Prop :=
  KOutRankLeOne p K ∧ KSylowTI p K ∧ KBorelMetabelian p K

@[expose] def KGenThree [Finite K] : Prop :=
  ∀ E : Subgroup (MulAut K), IsElemAbelian p E → 3 ≤ Open.pRank p E →
    Subgroup.closure {k : K | ∃ e ∈ E, e ≠ 1 ∧ e k = k} = ⊤

@[expose] def KOutNormalSylow [Finite K] : Prop :=
  ∀ S : Sylow p (MulAut K),
    ((MulAut.conj : K →* MulAut K).range ⊔ (S : Subgroup (MulAut K))).Normal

@[expose] def KOutTwoGroup : Prop :=
  ∀ f : MulAut K, ∃ k : ℕ, f ^ (2 ^ k) ∈ (MulAut.conj : K →* MulAut K).range

end Aut

@[expose] def KFactBeta : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K, (T : Subgroup K) ≠ ⊥ →
      (IsCyclic (T : Subgroup K) ∨ GLBCore p 1 (T : Subgroup K) ≠ ⊤) →
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 ∨ RankOneLieAutFacts p K


end CFSG.AGLEmbedding
