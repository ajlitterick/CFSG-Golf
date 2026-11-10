module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInnerInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenOuterInvolutions
public import CFSG.LieType.Chevalley.SignKernelComponentPerfect

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem even_G2_all_involution_full_centralizer_odd_core {f : ℕ} (hf : 2 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = 2 ^ f) (H : Subgroup (MulAut (adjointGroup .G2 K)))
    (hIH : inner (adjointGroup .G2 K) ≤ H) {α : MulAut (adjointGroup .G2 K)}
    (hα : orderOf α = 2) : CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ := by
  by_cases hαI : α ∈ inner (adjointGroup .G2 K)
  · exact even_G2_inner_involution_full_centralizer_odd_core hf K hK H hIH hαI hα
  · exact even_G2_outer_involution_full_centralizer_odd_core hf K hK H hIH hαI hα

end CFSG.ComponentClassification.UnbalancedCatalog
