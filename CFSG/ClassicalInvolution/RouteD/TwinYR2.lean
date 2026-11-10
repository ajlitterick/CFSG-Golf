module

public import CFSG.ClassicalInvolution.RouteD.TwinYP1Main

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

section Statement

variable (p f : ℕ) [Fact p.Prime]


end Statement

section Gen

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}

theorem genSection_of_loc (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hA : ∀ L ∈ Ω, AEmpty Ω L) : GenSection p f (locFamily Ω u) := by
  have hS := genSection_layerHull hp hq hΩ hA (Subgroup.centralizer ({u} : Set G))
  rw [layerHull_centralizer_eq, locFamily_eq] at hS
  exact hS

theorem normalClosure_le_centralizer_of_not_conj (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hA : ∀ L ∈ Ω, AEmpty Ω L) (hn : CITBelowU p f (Nat.card G))
    (hu : ¬ ({u} : Set G) ⊆ Subgroup.center G) {J M : Subgroup (locQuot Ω u)}
    (hJ : J ∈ locFamily Ω u) (hM : M ∈ locFamily Ω u)
    (hno : ∀ g : locQuot Ω u, conjSub g J ≠ M) :
    Subgroup.normalClosure (J : Set (locQuot Ω u)) ≤
      Subgroup.centralizer (M : Set (locQuot Ω u)) := by
  have hS := genSection_of_loc (u := u) hp hq hΩ hA
  have h4 : Thm4Below p f (Nat.card G) := thm4Below_of_citBelow hn
  have hlt := card_locQuot_lt (Ω := Ω) hu
  have hcomm : ∀ g : locQuot Ω u, Commutes (conjSub g J) M := by
    intro g
    refine h4 hp hq (locQuot Ω u) hlt (locFamily Ω u) hS.hyp hS.oddCore hS.aEmpty
      (conjSub g J) (hS.hyp.conjInvariant g J hJ) M hM ?_
    rintro ⟨h, hh⟩
    exact hno (h * g) (by rw [conjSub_mul]; exact hh)
  unfold Subgroup.normalClosure
  rw [Subgroup.closure_le]
  intro b hb
  obtain ⟨a, ha, hab⟩ := Group.mem_conjugatesOfSet_iff.mp hb
  obtain ⟨c, hc⟩ := isConj_iff.mp hab
  have hbmem : b ∈ conjSub c J := by
    rw [← hc]
    exact conj_mem_conjSub ha
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro m hm
  exact (hcomm c b hbmem m hm).symm

end Gen

section Trans


end Trans

end CFSG.ClassicalInvolution.RouteD.TwinY
