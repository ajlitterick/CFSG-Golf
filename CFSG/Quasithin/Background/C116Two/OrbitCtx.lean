module

public import CFSG.Quasithin.Background.C116Two.Ctx
public import CFSG.Quasithin.Background.C116Two.OrbitConj
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourConj

public section

namespace CFSG.Quasithin.C116Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem Ctx.conj {H T V L : Subgroup G} (h : Ctx H T V L) {a : G} (ha : a ∈ T) :
    Ctx H T V (conjByElt a L) := by
  have haH : a ∈ H := h.sylow.1 ha
  refine ⟨h.charTwo, h.red, h.sylow, ⟨IsBlock2.conjByElt_of_mem h.chi.1 haH, ?_⟩, ?_⟩
  · rcases h.chi.2 with ⟨n, hn, hlin⟩ | ⟨m, hm, hm3, halt⟩
    · exact Or.inl ⟨n, hn, Lin2.IsLin2Type.map_equiv hlin (MulAut.conj a)⟩
    · exact Or.inr ⟨m, hm, hm3, L238.IsAltType.map_equiv halt (MulAut.conj a)⟩
  · intro hle
    apply h.notCent
    intro l hl
    have hmem : a * l * a⁻¹ ∈ conjByElt a L := ⟨l, hl, by simp [MulAut.conj_apply]⟩
    have h1 := hle hmem
    have hN : a⁻¹ ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer V
        (h.red.2.1 (H.inv_mem haH))
    have := (Subgroup.mem_normalizer_iff.mp hN (a * l * a⁻¹)).mp h1
    simpa [mul_assoc] using this


end CFSG.Quasithin.C116Two
