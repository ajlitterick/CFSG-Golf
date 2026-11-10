module

public import CFSG.ClassicalInvolution.RouteD.TypeE8ExclR2Basic
public import CFSG.ClassicalInvolution.RouteD.TypeE8ExclR2Corr
public import CFSG.ClassicalInvolution.RouteD.TypeE8Attached
public import CFSG.ClassicalInvolution.RouteD.TypeE8Witness
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.NonClassical (mem_centralizingMembers_pair Linked NCEdge)
open CFSG.ClassicalInvolution.RouteD.Gaps (commutes_symm)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

omit [Finite G] in
theorem le_centralizer_mul_of_le {w₁ w₂ : G} {L : Subgroup G}
    (h₁ : L ≤ Subgroup.centralizer ({w₁} : Set G)) (h₂ : L ≤ Subgroup.centralizer ({w₂} : Set G)) :
    L ≤ Subgroup.centralizer ({w₁ * w₂} : Set G) := fun k hk => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have a := Subgroup.mem_centralizer_singleton_iff.mp (h₁ hk)
  have b := Subgroup.mem_centralizer_singleton_iff.mp (h₂ hk)
  calc k * (w₁ * w₂) = (k * w₁) * w₂ := by group
    _ = (w₁ * k) * w₂ := by rw [a]
    _ = w₁ * (k * w₂) := by group
    _ = w₁ * (w₂ * k) := by rw [b]
    _ = (w₁ * w₂) * k := by group

end CFSG.ClassicalInvolution.RouteD.TypeE8
