module

public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Defs

variable {G : Type} [Group G]

@[expose] def F112Concl (L1 L2 S : Subgroup G) : Prop :=
  ∃ L1' L2' : Subgroup G, ((L1' = L1 ∧ L2' = L2) ∨ (L1' = L2 ∧ L2' = L1)) ∧
    (centerOf S ≤ Subgroup.centralizer (L1 : Set G) ∨
        centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
      centerOf S ≤ Subgroup.centralizer (L1' : Set G)) ∧
    F112List L1' L2' S ∧ F112Second L1' L2' S


end Defs


variable {G : Type} [Group G]

theorem F112Hyp.symm [Finite G] {L1 L2 S : Subgroup G} (h : F112Hyp L1 L2 S) :
    F112Hyp L2 L1 S := by
  obtain ⟨⟨h1, h2, ho⟩, hq, hn⟩ := h
  refine ⟨⟨h2, h1, by rwa [sup_comm L2 L1]⟩, by rwa [sup_comm L2 L1], hn.symm⟩


theorem F112Concl.symm {L1 L2 S : Subgroup G} (h : F112Concl L1 L2 S) : F112Concl L2 L1 S := by
  obtain ⟨L1', L2', hsw, hZ, hl, h2⟩ := h
  exact ⟨L1', L2', hsw.symm, fun hc => hZ hc.symm, hl, h2⟩


end CFSG.Quasithin
