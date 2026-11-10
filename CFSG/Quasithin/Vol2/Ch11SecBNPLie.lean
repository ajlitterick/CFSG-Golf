module

public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Quasithin.Vol2.Ch11SecBNPE114

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

@[expose] def TypeLie (n : ℕ) (Y : Type) [Group Y] : Prop :=
  IsPSL 2 2 n Y ∨ IsSz n Y ∨ IsPSU 3 2 n Y ∨ IsPSL 3 2 n Y ∨ IsPSp4 2 n Y ∨
    (n = 1 ∧ IsAlt 6 Y)

theorem TypeLie.of_mulEquiv {n : ℕ} {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : TypeLie n Y') : TypeLie n Y := by
  rcases h with h | h | h | h | h | ⟨hn, h⟩
  · exact Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h)
  · exact Or.inr (Or.inl (CFSG.SectionRank.suzukiModel_of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h)))))
  · obtain ⟨e'⟩ : Nonempty (Y' ≃* alternatingGroup (Fin 6)) := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hn, ⟨e.trans e'⟩⟩))))

theorem TypeLie.isSimpleGroup {n : ℕ} {Y : Type} [Group Y] (h : TypeLie n Y) :
    IsSimpleGroup Y := by
  rcases h with h | h | h | h | h | ⟨-, h⟩
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 2 2 n h).2
  · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity Y 2 n h).2
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity Y 3 2 n h).2
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 3 2 n h).2
  · exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp Y 2 2 n h
  · obtain ⟨e⟩ : Nonempty (Y ≃* alternatingGroup (Fin 6)) := h
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup


end CFSG.Quasithin.Vol2.Ch11.SecB
