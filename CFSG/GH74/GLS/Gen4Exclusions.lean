module

public import CFSG.GH74.GLS.Assembly
public import CFSG.GH74.Filter.Sporadic.ON
public import CFSG.Sporadic.NativeFinite

public section

namespace CFSG.GH74

theorem SectionalTwoRankLE.of_sylow {X : Type*} [Group X] [Finite X] {r : ℕ} (S : Sylow 2 X)
    (h : SectionalTwoRankLE (S : Subgroup X) r) : SectionalTwoRankLE X r := by
  classical
  intro P hP
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S Q
  let f : (S : Subgroup X) →* X := (MulAut.conj g).toMonoidHom.comp (S : Subgroup X).subtype
  have hf : Function.Injective f := (MulAut.conj g).injective.comp Subtype.val_injective
  have hrange : P ≤ f.range := by
    intro x hx
    have hxQ : x ∈ (Q : Subgroup X) := hPQ hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
    obtain ⟨y, hy, rfl⟩ := hxQ
    exact ⟨⟨y, hy⟩, rfl⟩
  obtain ⟨s, hs, hsP⟩ := h (P.comap f) (hP.comap_of_injective f hf)
  refine ⟨s.image f, Finset.card_image_le.trans hs, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hsP, Subgroup.map_comap_eq,
    inf_eq_right.mpr hrange]


namespace GLS

open Blueprint Assembly.LowTwoRank


end GLS

end CFSG.GH74
