module

public import CFSG.LocalAnalysis.StandardType.GGD5Defs
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall
import CFSG.LocalAnalysis.StandardType.GGD5LabelExclLin
import CFSG.LocalAnalysis.StandardType.GGD5LabelExclSymp
import CFSG.LocalAnalysis.StandardType.GGD5LabelExclUnit
import CFSG.LocalAnalysis.StandardType.GGD5LabelExclOrth
import CFSG.LocalAnalysis.StandardType.GGD5LabelExclExc
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsOrder

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

theorem lup10d_label_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p = 3) (hxL : x ∉ L) {y : G} {H : Subgroup G} (M : GGQTwoAmbModel p Bs x y L H)
    (e : Fin 5 ≃ M.ι) (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j)
    (he0 : M.a = e 0) (hbas : M.toLin.Basis) :
    GGInnerDiagOnLabel (fun _ lab => lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = 1) p Bs L := by
  subst hp
  have hq : GGInnerDiagOnLabel (fun _ lab => (lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = 1) ∨
      ((lab.tag = .A ∨ (lab.tag = .twD ∧ lab.rank = 2) ∨ lab.tag = .triD4 ∨ lab.tag = .G2 ∨
        lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨
        lab.tag = .twF4der) ∧ lab.n = 1) ∨
      ((lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .F4) ∧ lab.n = 1) ∨
      ((lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧ lab.n = 1) ∨
      (((lab.tag = .D ∧ lab.rank ≠ 4) ∨ (lab.tag = .twD ∧ 4 ≤ lab.rank)) ∧ lab.n = 1) ∨
      ((lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .twE6) ∧ lab.n = 1))
      3 Bs L := by
    refine GGInnerDiagOnLabel.mono_label_of_hasLabel (fun lab hlab _ hn => ?_) hS.2.1
    have h1 : 1 ≤ lab.n := hlab.1
    have hn1 : lab.n = 1 := by
      have h2 : lab.n < 2 := hn
      omega
    obtain ⟨t, r, n⟩ := lab
    dsimp only at hn1 ⊢
    cases t
    case D =>
      by_cases hr : r = 4
      · exact Or.inl ⟨rfl, hr, hn1⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨rfl, hr⟩, hn1⟩))))
    case twD =>
      have hr2 : 2 ≤ r := hlab.2
      rcases (show r = 2 ∨ r = 3 ∨ 4 ≤ r by omega) with h | h | h
      · exact Or.inr (Or.inl ⟨Or.inr (Or.inl ⟨rfl, h⟩), hn1⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨rfl, h⟩, hn1⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨rfl, h⟩, hn1⟩))))
    all_goals simp [hn1]
  rcases GGInnerDiagOnLabel.elim_or hq with h | h
  · exact h
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · exact (lup10e_not_lin hS hxL M e hecart he0 hbas h).elim
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · exact (lup10e_not_symp hS hxL M e hecart he0 hbas h).elim
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · exact (lup10e_not_unit hS hxL M e hecart he0 hbas h).elim
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · exact (lup10e_not_orth hS hxL M e hecart he0 hbas h).elim
  · exact (lup10e_not_exc hS hxL M e hecart he0 hbas h).elim

end CFSG.StandardType

end
