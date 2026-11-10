module

public import CFSG.Quasithin.Background.C1GNC128
import CFSG.Foundations.KCoreClosure
public import CFSG.Quasithin.Background.C1GNA7
public import CFSG.Quasithin.EmptyFaithful.QTKELocal

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def TheoremC126 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (C₁ C₂ : Subgroup G → Subgroup G),
    IsGNChoice C₁ C₂ → C126Statement C₁ C₂


section Members

variable {G : Type} [Group G] [Finite G]

theorem kGroup_of_forall_commute {A : Type} [Group A] [Finite A] (h : ∀ a b : A, a * b = b * a) :
    CFSG.SectionRank.IsKGroupCat A :=
  CFSG.KCore.KGroupAllSimple.of_commutative CFSG.SectionRank.catalog_containsAbelianSimple h

theorem inM_facts (hsimple : IsSimpleGroup G) (hqtke : quasithinIsQTKECat G) {T M : Subgroup G}
    (hsyl : quasithinIsSylowTwo T) (hM : InM T M) :
    CharTwo M ∧ IsSQTKTC M ∧ IsSylowTwoOf T M := by
  have hTM : T ≤ M := hM.2
  have hSylM : IsSylowTwoOf T M :=
    ⟨hTM, hsyl.1, fun h => hsyl.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hTM))⟩
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hsyl
  have hMchar : CharTwo M := hqtke.2.1 M hM.1.1 ⟨S, hS ▸ hTM⟩
  have hO : pCoreOf 2 M ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hM.1.1
  refine ⟨hMchar, ⟨?_, stronglyQuasithin_of_pCoreOf_ne_bot hqtke hO⟩, hSylM⟩
  by_cases hnab : ∃ a b : G, a * b ≠ b * a
  · exact kGroup_of_pCoreOf_ne_bot hqtke hsimple hnab hO
  · push Not at hnab
    exact kGroup_of_forall_commute fun a b => Subtype.ext (hnab a b)

end Members


end CFSG.Quasithin
