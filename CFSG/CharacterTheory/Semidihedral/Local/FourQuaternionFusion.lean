module

public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionFusionSupport
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphismsSupport

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open

universe u

variable {G : Type u} [Group G] [Finite G]


theorem semidihedral_fusion_chain (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (P : Subgroup G) (hPS : P ≤ S) (g : G)
    (hg : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ S) :
    ∃ k : ℕ, ∃ c : SemidihedralFusionChain (S : Subgroup G) k,
      c.subgroups 0 = P ∧ c.subgroups (Fin.last k) = P.map (MulAut.conj g⁻¹).toMonoidHom ∧
      ∀ x : c.subgroups 0, (c.composite x : G) = g⁻¹ * (x : G) * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c₀, hc₀, hc₀g⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion S hPS hg
  obtain ⟨z, hz, hzc⟩ := semidihedralFusionDecomposition_of_alperin n hn S f hc₀
  obtain ⟨k, c, hfirst, hlast, hcomp⟩ := hz.exists_chain hPS
  refine ⟨k, c, hfirst, ?_, fun x => ?_⟩
  · rw [hlast]
    exact map_conj_inv_eq_of_pointwise P fun x hx => (hzc x hx).trans (hc₀g x hx)
  · have hx : (x : G) ∈ P := hfirst ▸ x.2
    rw [hcomp x]
    exact (hzc x hx).trans (hc₀g x hx)


end CFSG.Semidihedral.Local
