module

public import CFSG.Milestones.ASVolI.F429.bC3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

section Generic

theorem burnsideF429_index_dvd_card_outer {E : Type} [Group E] [Finite E] {Gp : Subgroup E}
    [Gp.Normal] (hc : Subgroup.centralizer (Gp : Set E) = ⊥) :
    Gp.index ∣ Nat.card (Outer ↥Gp) := by
  set α : E →* MulAut ↥Gp := MulAut.conjNormal with hα
  have hαinj : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hcg : g ∈ Subgroup.centralizer (Gp : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := congrArg (fun φ : MulAut ↥Gp => ((φ ⟨x, hx⟩ : ↥Gp) : E)) (MonoidHom.mem_ker.1 hg)
      simp only [hα, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc x * g = g * x * g⁻¹ * g := by rw [h1]
        _ = g * x := by group
    rw [hc] at hcg
    exact hcg
  have hG : Gp.map α = inner ↥Gp := by
    ext φ
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, MulEquiv.ext fun x => Subtype.ext (by
        simp [hα, MulAut.conjNormal_apply, MulAut.conj_apply])⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, MulEquiv.ext fun x => Subtype.ext (by
        simp [hα, MulAut.conjNormal_apply, MulAut.conj_apply])⟩
  have h1 : (Gp.map α).relIndex ((⊤ : Subgroup E).map α) = Gp.index := by
    rw [Subgroup.relIndex_map_map_of_injective _ _ hαinj, Subgroup.relIndex_top_right]
  rw [← h1, hG]
  have h2 : (inner ↥Gp).relIndex ((⊤ : Subgroup E).map α) ∣ (inner ↥Gp).index :=
    Subgroup.relIndex_dvd_index_of_le (hG ▸ Subgroup.map_mono le_top)
  exact h2


end Generic

section Kinds


end Kinds

end CFSG.ASVolI
