module

public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
public import CFSG.RankThree.PartTwo.Sec14.Concl143HJ
import CFSG.RankThree.PartTwo.Sec14.Item148ProofNHJ
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section Point

variable {A L : Subgroup G} {c : G}

theorem item143NAt_of_lB_eq_bot (hbal : Step143Balance) (h : Sec14Std G A c L) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) (hΩ : Subgroup.zpowers a ∉ omegaA A)
    (hLB : ∀ B : Subgroup G, IsHyperplane A B → a ∈ B → lB A B = ⊥) :
    Item143NAt A (lB A) a :=
  fun Q hQ => ⟨concl143_at_of_lB_eq_bot hbal h ha ha1 hΩ hLB Q hQ,
    Or.inl (delta_eq_sup_of_lB_eq_bot hbal h ha ha1 hΩ hLB)⟩

theorem forall_lB_eq_bot_or_exists_isLBConfig (A : Subgroup G) (a : G) :
    (∀ B : Subgroup G, IsHyperplane A B → a ∈ B → lB A B = ⊥) ∨
      ∃ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B ∧ a ∈ B ∧
        IsLBConfig A B b d Lb := by
  by_cases hall : ∀ B : Subgroup G, IsHyperplane A B → a ∈ B → lB A B = ⊥
  · exact Or.inl hall
  · push Not at hall
    obtain ⟨B, hB, haB, hne⟩ := hall
    obtain ⟨b, d, Lb, hc⟩ := exists_isLBConfig_of_lB_ne_bot hne
    exact Or.inr ⟨B, b, d, Lb, hB, haB, hc⟩

end Point

section Std

variable {A L : Subgroup G} {c : G}


section Certificates


theorem lB_eq_bot_of_not_allPointsHJ' (h134 : Item134) (h48 : Sec4.Item4_8)
    (h : Sec14Std G A c L) (hNHJ : ¬ AllPointsHJ A) {B : Subgroup G} (hB : IsHyperplane A B) :
    lB A B = ⊥ :=
  lB_eq_bot_of_not_allPointsHJ h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48
    Sec4.Sporadic.rank3II_4_15 (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15) h
    hNHJ hB


end Certificates

end Std


end CFSG.RankThree.PartTwo.Sec14
