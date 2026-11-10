module

public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Balance.QNineShapeU
public import CFSG.ClassicalInvolution.Balance.QNineModels
import CFSG.ClassicalInvolution.Balance.BootstrapExoticG2D4

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank

section Component

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)}

@[expose] def LocalLeviComponent (p f : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (Ω : Set (Subgroup G)) (x : G) : Prop :=
  ∃ D : LieSystemData p f (locQuot Ω x) (locFamily Ω x), ∃ i : Fin D.card,
    (D.tag i = .PSL ∧ 3 ≤ D.rank i) ∨ D.tag i = .PSU ∨ D.tag i = .PSp ∨ HasA2Pairs (D.tag i) ∨
      (p ^ f = 9 ∧ (D.tag i = .G2 ∨ D.tag i = .trialityD4))

theorem LocalLeviComponent.of_levi {x : G} (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    (i : Fin D.card)
    (h : (D.tag i = .PSL ∧ 3 ≤ D.rank i) ∨ D.tag i = .PSU ∨ D.tag i = .PSp ∨
      HasA2Pairs (D.tag i)) :
    LocalLeviComponent p f Ω x :=
  ⟨D, i, h.imp_right fun h => h.imp_right fun h => h.imp_right Or.inl⟩

theorem LocalLeviComponent.exists_member [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) {x : G} (h : LocalLeviComponent p f Ω x) :
    ∃ L ∈ centralizingMembers Ω {x}, LeviBlockImage p f (locImg Ω x L) := by
  obtain ⟨D, i, hi⟩ := h
  rcases hi with ⟨ht, hr⟩ | ht | ht | ha | ⟨h9, hex⟩
  · obtain ⟨k, hk⟩ : ∃ k, D.rank i = k + 1 := ⟨D.rank i - 1, by omega⟩
    exact exists_member_leviBlockImage_of_psl D i ht hk (by omega)
  · have hadm := D.admissible i
    rw [ht] at hadm
    exact exists_member_leviBlockImage_of_psu hp2 hq D i ht rfl hadm.2.2.1
  · have hadm := D.admissible i
    rw [ht] at hadm
    exact exists_member_leviBlockImage_of_psp D i ht rfl hadm.2.2.1
  · exact exists_member_leviBlockImage_of_a2Tag hp2 hq D i ha
  · exact exists_member_leviBlockImage_of_g2d4 hΩ h9 D i hex


theorem exactMembers_of_localLeviComponent [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {x : G}
    (hP1 : LocalOddCentral Ω {x}) (h : LocalLeviComponent p f Ω x) : ExactMembers Ω := by
  obtain ⟨L, hL, hlevi⟩ := h.exists_member hp2 hq hΩ
  exact exactMembers_of_leviBlockImage hp2 hq hΩ hsingle hP1 hL hlevi

end Component

section Stage


end Stage

end CFSG.ClassicalInvolution.Balance
