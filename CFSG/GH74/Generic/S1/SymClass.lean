module

public import CFSG.GH74.Generic.S1.GlueLinFull
public import CFSG.GH74.Generic.S1.GlueUni
public import CFSG.GH74.Generic.S1.GlueLin

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic

variable {G : Type} [Group G] [Finite G]

theorem not_goodFixed_conjNormal {x : G} (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)}
    [K.Normal] (hxK : xbar x ∈ K) (hfront : S1Front G x K) {v : G}
    (hv : v ∈ centralizer ({x} : Set G)) (hconj : IsConj x v) (hvx : v ≠ x) (hv2 : v * v = 1) :
    ¬ GoodFixedCentral (ThreeModel ↥K) (MulAut.conjNormal (barOf hv) : MulAut ↥K) := by
  rintro ⟨H, hfix, hz, hgood⟩
  refine false_of_goodFixed hx hfront.good_le hfront.b5 hv hconj hvx hv2 (H.map K.subtype)
    (map_subtype_le_centralizer H hfix) ?_ (goodSub_map K.subtype hgood)
  refine ⟨⟨xbar x, hxK⟩, hz _ ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (xbar_comm x (g : CentralizerBar x))

omit [Finite G] in
theorem conjNormal_involutory {x : G} {K : Subgroup (CentralizerBar x)} [K.Normal]
    (hcentle : Subgroup.centralizer (K : Set (CentralizerBar x)) ≤ K) {v : G}
    (hv : v ∈ centralizer ({x} : Set G)) (hv2 : v * v = 1) (hvK : barOf hv ∉ K) :
    (MulAut.conjNormal (barOf hv) : MulAut ↥K) * MulAut.conjNormal (barOf hv) = 1 ∧
      ∀ k : ↥K, (MulAut.conjNormal (barOf hv) : MulAut ↥K) ≠ MulAut.conj k := by
  have hbar2 : barOf hv * barOf hv = 1 := by
    have : proj x ((⟨v, hv⟩ : ↥(centralizer ({x} : Set G))) * ⟨v, hv⟩) = 1 := by
      rw [show (⟨v, hv⟩ : ↥(centralizer ({x} : Set G))) * ⟨v, hv⟩ = 1 from Subtype.ext hv2,
        map_one]
    rwa [map_mul] at this
  refine ⟨?_, fun k h => hvK (mem_of_conjNormal_inner hcentle h)⟩
  rw [← map_mul, hbar2, map_one]


end CFSG.GH74.Generic.S1
