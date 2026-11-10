module

public import CFSG.Open.FusionDefs
public import CFSG.Foundations.GilmanSolomonGrammar

public section

namespace CFSG.Open

open Subgroup

variable {G : Type*} [Group G]

@[expose] def fusionTwoComponentCond (L K : Subgroup G) : Prop :=
  CFSG.Open.IsSubnormal L K ∧ commutator L = ⊤ ∧ CFSG.Open.IsQuasisimple (L ⧸ fusionOddCore L)


@[expose] def fusionFixedLayer (N : Subgroup G) (t : G) : Subgroup G :=
  fusionTwoLayer (N ⊓ centralizer ({t} : Set G))

@[expose] def fusionUnbalancingTriple (a x : G) (J : Subgroup G) : Prop :=
  gs_grammar% GSGrammar.UnbalancingTriple fusionTwoComponentCond fusionOddCoreOf a x J

@[expose] def fusionCorr (a : G) (J : Subgroup G) (b : G) (L : Subgroup G) : Prop :=
  gs_grammar% GSGrammar.Corr fusionTwoComponentCond fusionOddCoreOf fusionFixedLayer a J b L

@[expose] def fusionIsoCorr (a : G) (J : Subgroup G) (b : G) (L : Subgroup G) : Prop :=
  gs_grammar% GSGrammar.IsoCorr fusionCorr fusionOddCoreOf fusionFixedLayer a J b L

@[expose] def fusionMaximalUnbalancingTriple (a x : G) (J : Subgroup G) : Prop :=
  gs_grammar% GSGrammar.MaximalUnbalancingTriple fusionUnbalancingTriple fusionCorr fusionIsoCorr
    a x J

@[expose] def fusionIsInvolutionTwoComponent (J : Subgroup G) : Prop :=
  gs_grammar% GSGrammar.InvolutionComponent fusionTwoComponentCond J

@[expose] def fusionReach (J L : Subgroup G) : Prop :=
  gs_grammar% GSGrammar.Reach fusionIsInvolutionTwoComponent fusionCorr J L

@[expose] def fusionMaximalComponent (J : Subgroup G) : Prop :=
  gs_grammar% GSGrammar.MaximalComponent fusionIsInvolutionTwoComponent fusionReach
    (fun H => fusionZStar H) J

theorem fusionUnbalancingTriple_iff_grammar {a x : G} {J : Subgroup G} :
    fusionUnbalancingTriple a x J ↔
      GSGrammar.UnbalancingTriple fusionTwoComponentCond fusionOddCoreOf a x J :=
  Iff.rfl

theorem fusionCorr_iff_grammar {a b : G} {J L : Subgroup G} :
    fusionCorr a J b L ↔
      GSGrammar.Corr fusionTwoComponentCond fusionOddCoreOf fusionFixedLayer a J b L :=
  Iff.rfl

theorem fusionIsoCorr_iff_grammar {a b : G} {J L : Subgroup G} :
    fusionIsoCorr a J b L ↔ GSGrammar.IsoCorr fusionCorr fusionOddCoreOf fusionFixedLayer a J b L :=
  Iff.rfl

theorem fusionMaximalUnbalancingTriple_iff_grammar {a x : G} {J : Subgroup G} :
    fusionMaximalUnbalancingTriple a x J ↔
      GSGrammar.MaximalUnbalancingTriple fusionUnbalancingTriple fusionCorr fusionIsoCorr a x J :=
  Iff.rfl

theorem fusionIsInvolutionTwoComponent_iff_grammar {J : Subgroup G} :
    fusionIsInvolutionTwoComponent J ↔ GSGrammar.InvolutionComponent fusionTwoComponentCond J :=
  Iff.rfl

theorem fusionReach_iff_grammar {J L : Subgroup G} :
    fusionReach J L ↔ GSGrammar.Reach fusionIsInvolutionTwoComponent fusionCorr J L :=
  Iff.rfl

theorem fusionMaximalComponent_iff_grammar {J : Subgroup G} :
    fusionMaximalComponent J ↔
      GSGrammar.MaximalComponent fusionIsInvolutionTwoComponent fusionReach
        (fun H => fusionZStar H) J :=
  Iff.rfl


theorem le_normalizer_fusionOddCoreOf (L : Subgroup G) :
    L ≤ normalizer (fusionOddCoreOf L : Set G) := by
  have hnormal : ((fusionOddCoreOf L).subgroupOf L).Normal := by
    rw [fusionOddCoreOf, ← comap_subtype, comap_map_eq_self_of_injective L.subtype_injective]
    infer_instance
  exact le_normalizer_of_normal_subgroupOf (map_subtype_le _)


theorem fusionIsSylowIn_iff {p : ℕ} {S H : Subgroup G} :
    fusionIsSylowIn p S H ↔ S ≤ H ∧ ∃ P : Sylow p ↥H, (P : Subgroup ↥H) = S.subgroupOf H := by
  constructor
  · rintro ⟨hSH, hS, hmax⟩
    refine ⟨hSH, ⟨⟨S.subgroupOf H, hS.comap_subtype, fun {Q} hQ hSQ => ?_⟩, rfl⟩⟩
    have h1 := hmax (Q.map H.subtype) (map_subtype_le Q) (hQ.map H.subtype) fun s hs =>
      ⟨⟨s, hSH hs⟩, hSQ (show (⟨s, hSH hs⟩ : H) ∈ S.subgroupOf H from hs), rfl⟩
    rw [← h1]
    exact (comap_map_eq_self_of_injective H.subtype_injective Q).symm
  · rintro ⟨hSH, P, hP⟩
    have hS : IsPGroup p S := by
      have h1 := P.isPGroup'.map H.subtype
      rwa [hP, map_subgroupOf_eq_of_le hSH] at h1
    refine ⟨hSH, hS, fun Q hQH hQ hSQ => ?_⟩
    have h1 := P.is_maximal' (Q := Q.subgroupOf H) hQ.comap_subtype (by
      rw [hP]
      exact fun x hx => hSQ hx)
    rw [hP] at h1
    have h2 := congrArg (Subgroup.map H.subtype) h1
    rwa [map_subgroupOf_eq_of_le hQH, map_subgroupOf_eq_of_le hSH] at h2


end CFSG.Open
