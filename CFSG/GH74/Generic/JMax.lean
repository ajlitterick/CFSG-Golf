module

public import CFSG.GH74.Generic.JMaxDefs
public import CFSG.GH74.Generic.Assembly

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.Blueprint

theorem exists_isJMax {G : Type} [Group G] [Finite G]
    (h : ∃ x : G, ∃ K : Subgroup (CentralizerBar x), G2Pair x K) :
    ∃ x : G, ∃ K : Subgroup (CentralizerBar x), IsJMax x K := by
  classical
  obtain ⟨x₀, K₀, h₀⟩ := h
  let P := {p : (Σ y : G, Subgroup (CentralizerBar y)) // G2Pair p.1 p.2}
  have : Nonempty P := ⟨⟨⟨x₀, K₀⟩, h₀⟩⟩
  obtain ⟨p₁, hp₁⟩ := Finite.exists_min (fun p : P => d2 ↥p.1.2)
  let Q := {p : P // d2 ↥p.1.2 = d2 ↥p₁.1.2}
  have : Nonempty Q := ⟨⟨p₁, rfl⟩⟩
  obtain ⟨q, hq⟩ := Finite.exists_max (fun q : Q => FRank ↥q.1.1.2)
  refine ⟨q.1.1.1, q.1.1.2, q.1.2, fun y L hL => ?_⟩
  have hmin : d2 ↥q.1.1.2 ≤ d2 ↥L := q.2.le.trans (hp₁ ⟨⟨y, L⟩, hL⟩)
  exact ⟨hmin, fun heq => hq ⟨⟨⟨y, L⟩, hL⟩, heq.trans q.2⟩⟩

@[expose] def S_shapeCaseMax
    (P : ∀ {G : Type} [Group G] (x : G), Subgroup (CentralizerBar x) → Prop) : Prop :=
  S_shapeCase (fun {G : Type} [Group G] (x : G) (K : Subgroup (CentralizerBar x)) =>
    IsJMax x K ∧ P x K)

theorem S_shapeCaseMax_of_S_shapeCase
    {P : ∀ {G : Type} [Group G] (x : G), Subgroup (CentralizerBar x) → Prop}
    (h : S_shapeCase @P) : S_shapeCaseMax @P :=
  fun G _ _ hs hn hr hgen hK hnab hL x hx K hKc hG2 hP =>
    h G hs hn hr hgen hK hnab hL x hx K hKc hG2 hP.2


end CFSG.GH74.Generic
