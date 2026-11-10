module

public import CFSG.LocalAnalysis.SectionRank.QTK.Interface

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem qtkSimpleList_of_exceptionalList {S : Type} [Group S] (h : QTExceptionalList S) :
    QTKSimpleList S := by
  rcases h with ⟨p, hp, hp2, hm⟩ | ⟨f, hf, hm⟩ | ⟨f, hf, hm⟩ | ⟨f, hodd, hf, hm⟩ | hm |
      ⟨f, hodd, hf, hm⟩
  · exact Or.inr (Or.inl ⟨p, hp, hp2, Or.inr (Or.inr (Or.inr (Or.inl hm)))⟩)
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hf, hm⟩)))))⟩)))
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨hf, hm⟩))))))⟩)))
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl ⟨hodd, hf, hm⟩)))))))⟩)))
  · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr hm))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr ⟨hodd, hf, hm⟩)))))))⟩)))

theorem qtkSimpleList_of_mem_qtkSporadicNames {S : Type} [Group S] {s : TauCeti.SporadicName}
    (hs : s ∈ qtkSporadicNames) (e : S ≃* NativeSporadic.Carrier s) : QTKSimpleList S := by
  refine Or.inr (Or.inr (Or.inr (Or.inr ⟨s, ?_, ⟨e⟩⟩)))
  simp only [qtkSporadicNames, Finset.mem_insert, Finset.mem_singleton] at hs
  exact hs


end CFSG.SectionRank.QTK
