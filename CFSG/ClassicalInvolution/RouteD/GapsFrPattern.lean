module

public import CFSG.ClassicalInvolution.RouteD.GapsFrZSide

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem toralNormalD_of_fixed_member {m : ℕ} (hm : 7 ≤ m) (c : TCtx p f .POmegaPlus m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus m Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfixM : HasFixedMember Ω K β z) :
    ToralNormalD c (partner_involution_commutes c.hp2 c.hz ht hKβ) := by
  obtain ⟨M, hMΩ, hKM, hβM, hMN⟩ := hfixM
  obtain ⟨u, rfl⟩ : ∃ u, m = u + 3 + 4 := ⟨m - 7, by omega⟩
  have hMN' : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N := by
    by_contra h
    exact hMN fun N hN hNM => by_contra fun hc => h ⟨N, hN, hNM, hc⟩
  obtain ⟨nd, h0, h1⟩ := exists_dnodes_of_pair (by omega) c hsingle hshape hβ ht hKβ hMΩ hKM hβM
  exact toralNormalD_of_nodes c ht hKβ hMΩ hMN' nd h0 h1

theorem PartnerPatternD.of_fixed_member {m : ℕ} (hm : 7 ≤ m) (hMFZ : FundNoncentral p)
    (c : TCtx p f .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus m Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfixM : HasFixedMember Ω K β z) :
    PartnerPatternD p f m Ω K β t :=
  PartnerPatternD.of_toral_normal_plus hm hMFZ c hsingle hshape hβ ht hKβ hfixM
    (toralNormalD_of_fixed_member hm c hsingle hshape hβ ht hKβ hfixM)

end CFSG.ClassicalInvolution.RouteD.Gaps
