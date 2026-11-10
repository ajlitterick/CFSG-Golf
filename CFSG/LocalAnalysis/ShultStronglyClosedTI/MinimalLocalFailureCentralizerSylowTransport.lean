module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityRestriction
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityActions
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityAlgebra
public import CFSG.StronglyEmbedded.BenderBorelTransport

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.CentralizerSylow

open CFSG.Open
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ShultStronglyClosedTI.TripleSylowMaximality

universe u

variable {G : Type u} [Group G]

theorem local_normalizer_internal_point_embedding [Finite G]
    (H Y : Subgroup G) (F : Subgroup Y)
    (hA : fusionStronglyEmbedded ((H.subgroupOf Y).subgroupOf F)) :
    fusionStronglyEmbedded (H.subgroupOf (F.map Y.subtype)) := by
  let E := F.map Y.subtype
  let e : F ≃* E := F.equivMapOfInjective Y.subtype Y.subtype_injective
  have he : ∀ x : F, (e x : G) = ((x : Y) : G) := fun _ => rfl
  have hmap : ((H.subgroupOf Y).subgroupOf F).map e.toMonoidHom =
      H.subgroupOf E := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      change (e a : G) ∈ H
      rw [he]
      exact ha
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      change ((e.symm x : Y) : G) ∈ H
      rw [← he, e.apply_symm_apply]
      exact hx
  rw [← hmap]
  exact hA.map_mulEquiv e


end CFSG.ShultStronglyClosedTI.CentralizerSylow
