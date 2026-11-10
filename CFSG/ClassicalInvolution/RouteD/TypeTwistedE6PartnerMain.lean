module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PartnerLink
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6Base
public import CFSG.ClassicalInvolution.RouteD.GapsConj
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Aux
public import CFSG.ClassicalInvolution.RouteD.NonClassicalTwin
public import CFSG.ClassicalInvolution.RouteD.TypeUFive

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem commutes_or_eq_at_conj (hMFZ : Gaps.FundNoncentral p) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {z})
    (Dz : LieSystemData p f (locQuot Ω z) (locFamily Ω z)) {g y : G} (hy : y = g * z * g⁻¹)
    {N L : Subgroup G} (hN : N ∈ centralizingMembers Ω {y}) (hL : L ∈ centralizingMembers Ω {y})
    (hcl : IsClassicalMember p f N y) : Commutes N L ∨ L = N := by
  subst hy
  obtain ⟨D', -, -⟩ := exists_lieSystemData_conj hΩ.conjInvariant g z Dz
  exact commutes_or_eq_of_involution hMFZ hΩ hex (localOddCentral_conj hΩ.conjInvariant g z hP1)
    D' hN hL hcl

theorem not_subset_center_mul (hMFZ : Gaps.FundNoncentral p) (c : UCtx p f 5 Ω K z) (nd : UNodes c)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (Dz : LieSystemData p f (locQuot Ω z) (locFamily Ω z)) :
    ¬ ({z * nd.w 0} : Set G) ⊆ Subgroup.center G := by
  intro hcen
  have hx : z * nd.w 0 ∈ Subgroup.center G := hcen rfl
  have h2' : (2 : GaloisField p f) ≠ 0 := two_ne_zero_of_charP_ne_two c.hp2
  obtain ⟨g, hg⟩ := hsingle (nd.j 0) (nd.mem 0 (by norm_num)).1
  have hw0 : nd.w 0 = g * z * g⁻¹ :=
    unique_involution_of_isClassicalMember h2' (c.hex (nd.j 0) (nd.mem 0 (by norm_num)).1)
      (nd.isCl 0 (by norm_num)) (hg ▸ c.hz.conj g)
  have h1w : nd.j 1 ≤ Subgroup.centralizer ({nd.w 0} : Set G) := by
    refine (le_centralizer_pair_mul_iff (nd.mem 1 (by norm_num)).2).mp fun n _ => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_center_iff.mp hx) n)
  have h0 : nd.j 0 ∈ centralizingMembers Ω {nd.w 0} :=
    ⟨(nd.mem 0 (by norm_num)).1, le_centralizer_of_isClassicalMember (nd.isCl 0 (by norm_num))⟩
  have h1 : nd.j 1 ∈ centralizingMembers Ω {nd.w 0} := ⟨(nd.mem 1 (by norm_num)).1, h1w⟩
  rcases commutes_or_eq_at_conj hMFZ c.hΩ c.hex c.hP1 Dz hw0 h0 h1 (nd.isCl 0 (by norm_num))
    with hc | heq
  · exact nd.adj 0 (by norm_num) hc
  · exact nd.inj 1 (by norm_num) 0 (by norm_num) (by norm_num) heq

@[expose] def TE6Adaptation (hf : 1 ≤ f) {c : UCtx p f 5 Ω K z} (nd : UNodes c) : Prop :=
  ∀ N : Subgroup G, N ∈ centralizingMembers Ω {z * nd.w 0} →
    (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K N) →
    (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W N (nd.j 0)) →
    ∃ V : Fin 3 → Subgroup G, IsTE6Base p f hf Ω K z V ∧ V 0 = nd.j 0 ∧
      Commutes N (V 1) ∧ Commutes N (V 2)


end CFSG.ClassicalInvolution.RouteD.NonClassical
