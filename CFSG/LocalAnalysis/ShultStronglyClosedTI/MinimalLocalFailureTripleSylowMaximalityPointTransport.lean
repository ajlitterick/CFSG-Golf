module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityStrongEmbedding
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.StrongEmbeddingMaximality
public import CFSG.StronglyEmbedded.BenderNormalSeries

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TripleSylowMaximality

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.OrderReductions.InvolutionGraph CFSG.OrderReductions.StrongEmbedding

universe u v

variable {G : Type u} [Group G] [Finite G]

theorem rank_two_stronglyEmbedded_action_double_transitive
    {Ω : Type v} [MulAction G Ω]
    (htrans : MulAction.IsPretransitive G Ω) (alpha : Ω)
    (hH : fusionStronglyEmbedded (MulAction.stabilizer G alpha))
    (hrank : TwoRankAtLeastTwo G) :
    MulAction.IsMultiplyPretransitive G Ω 2 := by
  let H := MulAction.stabilizer G alpha
  have horder := fusionStronglyEmbedded_to_orderReduction H hH
  let base : Conjugates H := ⟨H, ⟨1, one_smul G H⟩⟩
  have hbase : MulAction.stabilizer G base = H :=
    conjugate_stabilizer_eq H horder base
  have hcoset : MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 := by
    have h := (actionCoset_two_pretransitive_iff
      (inferInstance : MulAction.IsPretransitive G (Conjugates H)) base).mpr
        (rank_two_strongEmbedding_conjugates_double_transitive hrank H hH)
    rwa [hbase] at h
  exact (actionCoset_two_pretransitive_iff htrans alpha).mp hcoset


end CFSG.ShultStronglyClosedTI.TripleSylowMaximality
