module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelSylow
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelMaximal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CatalogueBOrthogonalSmallFamilyOrbit CatalogueBOrthogonalPointPlusFamilyOrbit
open scoped Pointwise

variable {n : ℕ} {K : Type} [Field K]

theorem charP_of_card {p f : ℕ} [Finite K] (hp : p.Prime) (hK : Nat.card K = p ^ f) :
    CharP K p := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hK)


theorem orthogonal_geometry_plus_model_maximal_Borel_overgroups {G : Type} [Group G]
    {p f : ℕ} (h : StatedClassicalModel G .POmegaPlus n p f) [Finite K]
    (M : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K))))
    (hM : IsCoatom M) (hBM : plusProjectiveBorel n K ≤ M) :
    (∃ i : ℕ, 1 ≤ i ∧ i ≤ n - 2 ∧
      M = statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K i)) ∨
    M = statedProjectiveSubspaceStabilizer (StatedQuadPlus n K)
      (Xstar n K (by have := h.1.2.2; omega)) ∨
    M = statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K n) :=
  plusProjectiveMaximalBorel_overgroups n K (by have := h.1.2.2; omega) M hM hBM

end CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
