module

public import CFSG.ClassicalInvolution.RouteD.TypeEMain
public import CFSG.ClassicalInvolution.RouteD.LocalTwinAdaptConj
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Final

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub FundamentalSingleClass
  fundamentalSubgroups modelUniv InClass IsClassicalMember LocalOddCentral ExactMembers
  centralizingMembers LieSystemData ConjInvariant centralizingLayer_le_centralizer)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

namespace ETCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem locLayer_le_normalizer (c : ETCtx p f tY nY Ω K z) :
    locLayer Ω z ≤ Subgroup.normalizer (K : Set G) := by
  refine iSup₂_le fun L hL => ?_
  by_cases hLK : L = K
  · subst hLK
    exact Subgroup.le_normalizer
  · refine le_trans (fun x hx => ?_) (Subgroup.centralizer_le_normalizer (K : Set G))
    exact Subgroup.mem_centralizer_iff.mpr fun k hk => c.commutes_K_of_ne hL hLK k hk x hx

end ETCtx

section NodeSystems

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}

theorem NodeSystem.conjSub {r : ℕ} {adj : Fin r → Fin r → Prop} {j : Fin r → Subgroup G}
    (hj : NodeSystem p f adj Ω K z j) (hΩ : ConjInvariant Ω) {y : G} (hyz : y * z * y⁻¹ = z)
    (hyK : y ∈ Subgroup.normalizer (K : Set G)) :
    NodeSystem p f adj Ω K z (fun a => CFSG.ClassicalInvolution.Generic.conjSub y (j a)) where
  mem a := by
    have := centralizingMembers_conj hΩ y z
    rw [hyz] at this
    rw [this]
    exact ⟨j a, hj.mem a, rfl⟩
  ne_K a := by
    intro h
    apply hj.ne_K a
    have := congrArg (CFSG.ClassicalInvolution.Generic.conjSub y⁻¹) h
    rw [CFSG.ClassicalInvolution.Generic.conjSub_inv_conjSub,
      conjSub_eq_of_mem_normalizer (inv_mem hyK)] at this
    exact this
  commK a := commutes_conjSub_of_mem_normalizer hyK (hj.commK a)
  comm a b hab h1 h2 := (hj.comm a b hab h1 h2).conjSub y
  pair a b h := by
    obtain ⟨W, hW⟩ := hj.pair a b h
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW y⟩

end NodeSystems

section Nodes

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}


theorem ETCtx.exists_nodeSystem_D6' (c : ETCtx p f .POmegaPlus 6 Ω K z)
    (hadm : StatedLieAdmissible .POmegaPlus 6 p f) :
    ∃ j : Fin 6 → Subgroup G, NodeSystem p f (edgeD 6) Ω K z j ∧
      ∀ a, locImg Ω z (j a) =
        (rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup a).map c.d.ψ := by
  have hp : p.Prime := Fact.out
  have hl := ModelFacts.isLongestRoot_single .POmegaPlus 6 p f hp trivial hadm
  obtain ⟨j, hj, hcomm, hpair, hK⟩ := c.exists_nodes (r := 6)
    (fun a => rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup a)
    (fun a => rankOne_mem_fundamental _ (hl a trivial)) (edgeD 6)
    (fun a b hab h1 h2 => commutes_rankOne_plusDatum (n := 6) (K := GaloisField p f)
      (by norm_num) (LevisSpin.cartanD_of_not_edgeD hab h1 h2).1)
    (fun a b h => standardPair_plusDatum_edge (F := GaloisField p f) (by norm_num) h)
  exact ⟨j, ⟨fun a => (hj a).1, fun a => (hj a).2.1, hK, hcomm, hpair⟩, fun a => (hj a).2.2⟩

theorem ETCtx.exists_nodeSystem_E7' (c : ETCtx p f .E7 0 Ω K z)
    (hadm : StatedLieAdmissible .E7 0 p f) :
    ∃ j : Fin 7 → Subgroup G, NodeSystem p f (edgeE 7) Ω K z j ∧
      ∀ a, locImg Ω z (j a) =
        (rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup a).map c.d.ψ := by
  have hp : p.Prime := Fact.out
  have hl := ModelFacts.isLongestRoot_single .E7 0 p f hp trivial hadm
  obtain ⟨nW, H, -, hext⟩ := ModelFacts.hasBruhatDatum .E7 0 p f hp trivial hadm
  have hdiv : (modelUniv .E7 0 p f Fact.out).D.divisible = ∅ := rfl
  have hℓ := lenSq_eq_of_simplyLaced (modelUniv .E7 0 p f Fact.out).D hdiv
    (fun i => hl i trivial) ⟨0, by show 0 < 7; decide⟩
  obtain ⟨j, hj, hcomm, hpair, hK⟩ := c.exists_nodes (r := 7)
    (fun a => rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup a)
    (fun a => rankOne_mem_fundamental _ (hl a trivial)) (edgeE 7)
    (fun a b hab h1 h2 => commutes_rankOne_of_cartan_eq_zero _ hext hℓ
      ((WeakCT.edgeE_orientation (τ := .E7) (Or.inr (Or.inl rfl))).2.2.1 a b hab h1 h2).1)
    (fun a b h => stdPair_edge_E7 h)
  exact ⟨j, ⟨fun a => (hj a).1, fun a => (hj a).2.1, hK, hcomm, hpair⟩, fun a => (hj a).2.2⟩

end Nodes

section Route

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G} {tY : StatedLieTag}
  {nY : ℕ}


variable [Finite G]


end Route

section Main

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}


theorem routeD_typeE7_of_exists [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 1 .POmegaPlus 6 Ω z)
    (hP1 : LocalOddCentral Ω {z})
    (hpartner : ∃ j : Fin 6 → Subgroup G,
      NodeSystem p f (edgeD 6) Ω K z j ∧ (PartnerAt p f Ω j 4 ∨ PartnerAt p f Ω j 5)) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .E7 ∧ D.rank i = 0 := by
  obtain ⟨j, hj, hβ⟩ := hpartner
  rcases hβ with h4 | h5
  · obtain ⟨U, hUΩ, hcomm, hpair⟩ := chainE7_of_partner hj h4
    exact routeD_typeE7_of_chain hp2 hq hΩ hK hsingle hconn hz hshape hP1 U hUΩ hcomm hpair
  · have hj' := hj.comp_equiv (Equiv.swap (4 : Fin 6) 5) edgeD6_swap
    have h5' : PartnerAt p f Ω (j ∘ Equiv.swap (4 : Fin 6) 5) 4 :=
      PartnerAt.comp_equiv (Equiv.swap (4 : Fin 6) 5) (by rwa [Equiv.swap_apply_left])
    obtain ⟨U, hUΩ, hcomm, hpair⟩ := chainE7_of_partner hj' h5'
    exact routeD_typeE7_of_chain hp2 hq hΩ hK hsingle hconn hz hshape hP1 U hUΩ hcomm hpair

theorem routeD_typeE8_of_exists [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 1 .E7 0 Ω z)
    (hP1 : LocalOddCentral Ω {z})
    (hpartner : ∃ j : Fin 7 → Subgroup G,
      NodeSystem p f (edgeE 7) Ω K z j ∧ PartnerAt p f Ω j 6) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .E8 ∧ D.rank i = 0 := by
  obtain ⟨j, hj, hβ⟩ := hpartner
  obtain ⟨U, hUΩ, hcomm, hpair⟩ := chainE8_of_partner hj hβ
  exact routeD_typeE8_of_chain hp2 hq hΩ hK hsingle hconn hz hshape hP1 U hUΩ hcomm hpair


end Main

end CFSG.ClassicalInvolution.RouteD
