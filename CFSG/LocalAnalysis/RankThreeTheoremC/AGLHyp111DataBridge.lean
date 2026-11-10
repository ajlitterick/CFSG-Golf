module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def Hyp111B3 (p : ℕ) (H Q : Subgroup G)
    (J : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop :=
  ∀ S : Subgroup G, IsPGroup 2 S → S ≤ H → Q ≤ Subgroup.normalizer (S : Set G) →
    S ≤ d1PlusCore p H J

structure Hyp111NineThree (p : ℕ) (M H : Subgroup G)
    (J : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop where
  normal : J.Normal
  plusCore_le : d1PlusCore p H J ≤ M
  factor : ∀ x ∈ H, ∃ m ∈ H ⊓ M, ∃ k : H, QuotientGroup.mk' _ k ∈ J ∧ x = m * k

theorem le_normalizer_d1PlusCore {p : ℕ} {H : Subgroup G}
    {J : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hJ : J.Normal) :
    H ≤ Subgroup.normalizer (d1PlusCore p H J : Set G) := by
  haveI := hJ
  have hC : (Subgroup.centralizer (J : Set (H ⧸ primeComplementCore (G := H) p))).Normal :=
    inferInstance
  have hN : ((Subgroup.centralizer (J : Set (H ⧸ primeComplementCore (G := H) p))).comap
      (QuotientGroup.mk' (primeComplementCore (G := H) p))).Normal := hC.comap _
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp ?_
  have e : (((Subgroup.centralizer (J : Set (H ⧸ primeComplementCore (G := H) p))).comap
      (QuotientGroup.mk' (primeComplementCore (G := H) p))).map H.subtype).subgroupOf H =
      (Subgroup.centralizer (J : Set (H ⧸ primeComplementCore (G := H) p))).comap
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [e]
  exact hN


theorem map_primeComplementCore_eq (p : ℕ) (H : Subgroup G) :
    (primeComplementCore (G := H) p).map H.subtype = GLBPrimeCore p H := by
  rw [glbPrimeCore_eq_primeComplementCoreOf]
  rfl

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
