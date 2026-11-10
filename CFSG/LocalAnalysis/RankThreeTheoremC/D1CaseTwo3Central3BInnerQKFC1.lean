module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQKFC1Cent
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQKFC1Aut
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQResidueLeaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQKFAThree
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3ReducedA
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.PreuniquenessRankFour.Helpers

@[expose] def KFactU33SylowIrr : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X),
    (∃ q : TauCeti.PrimePower, q.p = 3 ∧ q.card = 3 ∧
      CFSG.RankThree.PartOne.Census3.IsoLie ↥K (.twistedA 2 q)) →
    ∀ B : Subgroup X, B ≤ K → IsPGroup 3 B → ¬ 3 ∣ B.relIndex K →
      ∀ D : Subgroup X, D ≤ B → K ⊓ normalizer (B : Set X) ≤ normalizer (D : Set X) →
        D ≤ (frattini ↥B).map B.subtype ∨ D = B


namespace InnerQ.KFC1

variable {X : Type} [Group X] [Finite X] {T : Sylow 3 X} {X₀ : Subgroup X} {x : X}


theorem coe_mem_normalizer_map {K : Subgroup X} {H : Subgroup K} {n : K}
    (hn : n ∈ normalizer (H : Set K)) :
    (n : X) ∈ normalizer ((H.map K.subtype : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff]
  intro y
  by_cases hy : y ∈ K
  · constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨_, (mem_normalizer_iff.mp hn d).mp hd, rfl⟩
    · rintro ⟨d, hd, hdy⟩
      have : (⟨y, hy⟩ : K) ∈ H := (mem_normalizer_iff.mp hn ⟨y, hy⟩).mpr (by
        rw [show n * ⟨y, hy⟩ * n⁻¹ = d from Subtype.ext hdy.symm]
        exact hd)
      exact ⟨_, this, rfl⟩
  · refine iff_of_false (fun ⟨d, _, hdy⟩ => hy (hdy ▸ d.2)) fun ⟨d, _, hdy⟩ => hy ?_
    have hdy' : (d : X) = n * y * (n : X)⁻¹ := hdy
    have h := mul_mem (mul_mem (inv_mem n.2) d.2) n.2
    rw [hdy'] at h
    simpa [mul_assoc] using h

end InnerQ.KFC1


end CFSG.LocalAnalysis.RankThreeTheoremC
