module

public import CFSG.Quasithin.Vol2.Ch11SecBNPAut
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Background.InternalSecTwo
public import CFSG.Quasithin.Background.E1Invariance

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

@[expose] def TypeOne (Y : Type) [Group Y] : Prop :=
  IsPSL 3 2 1 Y ∨ IsAlt 6 Y ∨ (∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 < p ^ e ∧ IsPSL 2 p e Y) ∨
    ∃ (s : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ IsPSLEps3 s p 1 Y

theorem TypeOne.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : TypeOne Y') : TypeOne Y := by
  rcases h with h | h | ⟨p, f, hp, hp2, h5, h⟩ | ⟨s, p, hp, hp2, h⟩
  · exact Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h)
  · obtain ⟨e'⟩ : Nonempty (Y' ≃* alternatingGroup (Fin 6)) := h
    exact Or.inr (Or.inl ⟨e.trans e'⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨p, f, hp, hp2, h5, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨s, p, hp, hp2, ?_⟩))
    cases s with
    | true => exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h
    | false => exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h


theorem sqtkGroup_of_mulEquiv {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (h : SQTKGroup B) : SQTKGroup A := by
  refine ⟨fun p hp hp2 => ?_, h.2.of_mulEquiv e⟩
  have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup B) ≤ 2 := h.1 p hp hp2
  show CFSG.Open.pRank p (⊤ : Subgroup A) ≤ 2
  omega

theorem sqtkGroup_subgroup {A : Type} [Group A] [Finite A] (h : SQTKGroup A) (K : Subgroup A) :
    SQTKGroup ↥K := by
  refine ⟨fun p hp hp2 => ?_, h.2.subgroup K⟩
  have h1 := CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt K.subtype K.subtype_injective
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup A) ≤ 2 := h.1 p hp hp2
  show CFSG.Open.pRank p (⊤ : Subgroup ↥K) ≤ 2
  omega


end CFSG.Quasithin.Vol2.Ch11.SecB
