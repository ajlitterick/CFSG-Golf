module

public import CFSG.Quasithin.EmptyFaithful.S151cA1
public import CFSG.Quasithin.EmptyFaithful.T1515C6Top
public import CFSG.Quasithin.EmptyFaithful.T1515C7Fin
public import CFSG.Quasithin.EmptyFaithful.T1515Der5
public import CFSG.Quasithin.EmptyFaithful.T1515M11D4
public import CFSG.Quasithin.EmptyFaithful.T1515M11U

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def Lemma15123Standalone : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → ¬ Ce15Six T Mc M 5


section Chain

variable {G : Type} [Group G] [Finite G]

theorem ce15Small_of_not_six_five {T Mc M : Subgroup G} (hce : Ce15 T Mc M)
    (h5 : ¬ Ce15Six T Mc M 5) : Ce15Small T Mc M := by
  rcases hce with h | ⟨p, hp, h⟩ | h
  · exact Or.inl h
  · rcases hp with rfl | rfl
    · exact Or.inr (Or.inl h)
    · exact (h5 h).elim
  · exact Or.inr (Or.inr h)


theorem exists_setting_of_ce15Small (h15 : StageLemma1515CE) (h157 : StageLemma1517)
    (h19 : StageLemma1519) (h110 : StageLemma15110) (h113 : StageLemma15113)
    {T Mc M : Subgroup G} (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (hCE : IsCE1513 T M) (hsmall : Ce15Small T Mc M) :
    ∃ Z₁ Z₂ V₁ V₂ : Subgroup G, Setting1516X T Mc M Z₁ Z₂ V₁ V₂ := by
  rcases hsmall with h4 | h6 | h7
  · exact exists_setting_four hq hM h4 (h15 G T Mc M hq hM hCE) (h157 G T Mc M hq hM hCE)
      (h19 G T Mc M hq hM hCE) (h113 G T Mc M hq hM hCE).four
  · exact exists_setting_six3 hq hM h6 (h15 G T Mc M hq hM hCE) (h19 G T Mc M hq hM hCE)
      (h110 G T Mc M hq hM hCE h6) (h113 G T Mc M hq hM hCE).four
  · exact exists_setting_seven hq hM h7 (h15 G T Mc M hq hM hCE) (h19 G T Mc M hq hM hCE)
      (h113 G T Mc M hq hM hCE).four

end Chain


end CFSG.Quasithin
