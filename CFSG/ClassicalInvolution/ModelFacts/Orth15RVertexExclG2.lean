module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RG2Pair
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RVertexExcl

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.G2D4Models
open CFSG.Open (IsElemAbelian classicalInvolutionOddCore)
open scoped commutatorElement MatrixGroups

section Vertex

variable {p f : ℕ} [Fact p.Prime]

theorem false_of_g2_twin_sec (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω) {c : G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hAsec : ∀ K ∈ secFam Ω c, AEmpty (secFam Ω c) K)
    (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card) (hG2 : D.tag j = .G2)
    {M M' : Subgroup G} {b : G} (hM : M ∈ tqMembers Ω c) (hM' : M' ∈ tqMembers Ω c)
    (hMb : IsClassicalMember p f M b) (hM'b : IsClassicalMember p f M' b) (hne : M' ≠ M)
    (hMj : modOdd c (exactCore c M) ≤
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range)
    (hM'j : modOdd c (exactCore c M') ≤
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range) : False := by
  have hs' : SecData p f c (exactFamily Ω c) :=
    secData_exactFamily hΩ.conjInvariant hΩ.classical hc2 ⟨M, hM⟩
  obtain ⟨R, R', z, hR, hR', hKR, hK'R', hzKR, hzK'R', hneR⟩ :=
    twin_pair_in_sec hp hq hΩ hc2 D j hM hM' hMb hM'b hne hMj hM'j
  exact false_of_twin_g2 hp hq (hypOmega_secFam hp hq hΩ hc2 hs' D) hAsec
    (LieSystemData.toOmegaLie D (omegaGen_secFam hs')) (i := j) hG2 hR hR' hKR hK'R' hzKR hzK'R'
    hneR

@[expose] def SecAEmpty (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      (∀ M ∈ Ω, AEmpty Ω M) → ∀ c : G, IsPGroup 2 (Subgroup.zpowers c) →
        (tqMembers Ω c).Nonempty → ∀ K ∈ secFam Ω c, AEmpty (secFam Ω c) K

theorem g2VertexExcl_of_secAEmpty (h : SecAEmpty p f) : G2VertexExcl p f := by
  intro hp hq G _ _ Ω hΩ hA c hc2 D j hG2 M M' b hM hM' hMb hM'b hne hMj hM'j
  exact false_of_g2_twin_sec hp hq hΩ hc2 (h hp hq G Ω hΩ hA c hc2 ⟨M, hM⟩) D j hG2 hM hM' hMb
    hM'b hne hMj hM'j

end Vertex

section Centralizing


end Centralizing

end CFSG.ClassicalInvolution.Asc77
