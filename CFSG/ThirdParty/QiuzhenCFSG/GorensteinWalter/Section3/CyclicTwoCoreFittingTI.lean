module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finite.Defs
public import Mathlib.GroupTheory.NoncommCoprod

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCorePInfPg
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.HhatConjugateTI
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FUFittingContainment
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma25
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 3: the Fitting subgroup `F(U)` is a TI-subgroup

In the cyclic first case, the paper's line L512 asserts `P ∩ P^g = 1` for
`g ∉ N_H(V₁)`, and line L513--L514 conclude that `P·P^g` is an abelian
direct product.  The stronger normalizer-control statement proved here is
the full `F(U) ∩ F(U)^g = 1` for every `g ∉ Ĥ`, obtained by the same
`lemma_2_5` pattern used in `OddQCoreCentralized.lean`: the intersection
`X = F(U) ∩ F(U)^g` is transported back by `g⁻¹` into `F(U)`, where the
conjugated first-case normalizer clause (2) controls its normalizer;
Lemma 2.5 then forces `g ∈ Ĥ`.

The direct-product corollaries are stated abstractly: for commuting
subgroups with trivial intersection their join is isomorphic to their
product, and if both factors are abelian the join is abelian.  In the
first-case application the commuting hypothesis is supplied by normality
in `C_U(t₁)`.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- The join of two commuting subgroups with trivial intersection is
isomorphic to their direct product. -/
public noncomputable def subgroup_sup_equiv_prod_of_commute_of_disjoint
    {G : Type u} [Group G]
    (H K : Subgroup G)
    (hdisj : H ⊓ K = ⊥)
    (hcomm : ∀ h k, h ∈ H → k ∈ K → Commute h k) :
    ↥(H ⊔ K) ≃* (↥H) × (↥K) := by
  classical
  let f : H →* G := H.subtype
  let k : K →* G := K.subtype
  let hcomm' : ∀ h : H, ∀ kh : K, Commute (f h) (k kh) :=
    fun h kh => hcomm h.1 kh.1 h.2 kh.2
  let φ : (↥H) × (↥K) →* G :=
    f.noncommCoprod k hcomm'
  have hφinj : Function.Injective φ := by
    dsimp [φ]
    rw [MonoidHom.noncommCoprod_injective f k hcomm']
    refine ⟨Subgroup.subtype_injective _, Subgroup.subtype_injective _, ?_⟩
    rw [disjoint_iff_inf_le]
    intro x hx
    have hxH : x ∈ H := by
      rcases (Subgroup.mem_inf.mp hx).1 with ⟨h, rfl⟩
      exact h.2
    have hxK : x ∈ K := by
      rcases (Subgroup.mem_inf.mp hx).2 with ⟨g, rfl⟩
      exact g.2
    have hbot : x ∈ (⊥ : Subgroup G) := by
      rw [← hdisj]
      exact Subgroup.mem_inf.mpr ⟨hxH, hxK⟩
    exact Subgroup.mem_bot.mp hbot
  let e : (↥H) × (↥K) ≃* φ.range := MonoidHom.ofInjective hφinj
  have hφrange : φ.range = H ⊔ K := by
    have h := MonoidHom.noncommCoprod_range f k
      (fun h kh => hcomm h.1 kh.1 h.2 kh.2)
    simpa [f, k, Subgroup.range_subtype] using h
  exact (e.trans (MulEquiv.subgroupCongr hφrange)).symm

/-- The join of two commuting abelian subgroups with trivial intersection is
abelian. -/
public theorem subgroup_sup_isMulCommutative_of_commute_of_disjoint
    {G : Type u} [Group G]
    (H K : Subgroup G)
    (hdisj : H ⊓ K = ⊥)
    (hcomm : ∀ h k, h ∈ H → k ∈ K → Commute h k)
    (hHabel : IsMulCommutative (↥H)) (hKabel : IsMulCommutative (↥K)) :
    IsMulCommutative (↥(H ⊔ K)) := by
  classical
  have : IsMulCommutative (↥H) := hHabel
  have : IsMulCommutative (↥K) := hKabel
  let e := subgroup_sup_equiv_prod_of_commute_of_disjoint H K hdisj hcomm
  rw [isMulCommutative_iff]
  intro a b
  exact e.injective (by
    have hprod : IsMulCommutative ((↥H) × (↥K)) := inferInstance
    calc
      e (a * b) = e a * e b := e.map_mul a b
      _ = e b * e a := (isMulCommutative_iff.mp hprod) (e a) (e b)
      _ = e (b * a) := (e.map_mul b a).symm)


end CFSG.GorensteinWalter
