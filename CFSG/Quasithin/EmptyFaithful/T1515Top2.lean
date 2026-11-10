module

public import CFSG.Quasithin.EmptyFaithful.T1515Main
public import CFSG.Quasithin.EmptyFaithful.T1515AS116
public import CFSG.Quasithin.EmptyFaithful.T1515Der2
public import CFSG.Quasithin.EmptyFaithful.T1515Der

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]


@[expose] def Lemma15125InputRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Concl T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15122Concl T Mc M Z₁ L →
    Lemma15124Concl T Mc M Z₁ V₁ V₂ L →
    L = oPrimeResidualOf 3 (g1_1516 Z₁) ∧ ¬ V₁ ≤ Subgroup.centralizer (L : Set G) ∧
      ¬ IsAltBlockType L 7


end CFSG.Quasithin
