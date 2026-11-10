module

public import CFSG.RankThree.PartOne.S11d.LieCentralizerGL
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedCoverage
public import CFSG.RankThree.PartOne.KC.OrthogonalLocalComponents
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarElementary
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG Polynomial Module CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement


theorem eq_one_of_mem_scalars_of_mem_orthDerived {K : Type*} [Field K] [CharP K 2] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) [Nontrivial V] {g : V ≃ₗ[K] V}
    (hg : g ∈ orthDerived Q) (hs : g ∈ scalars K V) : g = 1 := by
  obtain ⟨c, hc⟩ := mem_scalars.mp hs
  obtain ⟨v, hv⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hQ
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup hg
  have h1 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO v
  rw [hc, QuadraticMap.map_smul, smul_eq_mul] at h1
  have hcc : c * c = 1 := by
    have := mul_right_cancel₀ hv (show c * c * Q v = 1 * Q v by rw [one_mul]; exact h1)
    exact this
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hc1 : c = 1 := by
    have h8 : (c - 1) ^ 2 = 0 := by
      have : (c - 1) ^ 2 = c * c - 1 - 2 * (c - 1) := by ring
      rw [this, hcc, h2]
      ring
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h8)
  exact LinearEquiv.ext fun u => by rw [hc, hc1, one_smul]; rfl


end CFSG.RankThree.PartOne
