module

public import CFSG.RankThree.PartTwo.KFacts.AutKinds
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable (r : ℕ) (K : Type) [Field K]

theorem conj_proj_eq_spConjAut (g : StatedSp r K) :
    MulAut.conj (proj r K g) = conjAut r K ⟨g, statedSp_le_gsp g.2⟩ := by
  ext x
  obtain ⟨h, rfl⟩ := proj_surjective x
  rw [MulAut.conj_apply, conjAut_proj, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg (proj r K) (Subtype.ext rfl)

theorem innAut_le_range_spConjAut :
    (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      (conjAut r K).range := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨g, rfl⟩ := proj_surjective x
  exact ⟨_, (conj_proj_eq_spConjAut r K g).symm⟩

@[expose] noncomputable def stdPinnedPSp : PinnedAut (StatedProj (StatedSp r K)) where
  inndiag := (conjAut r K).range
  inn_le := innAut_le_range_spConjAut r K
  field := (fieldAut r K).range
  graph := ∅

variable {r K}


section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

variable (r K) in
@[expose] def InducesKindPSp (x : G) (k : AutKind) : Prop :=
  ∃ e : L ⧸ aschbacherSolvableCore 3 L ≃* StatedProj (StatedSp r K),
    InducesKind L (stdPinnedPSp r K) e x k


end Induced

end CFSG.RankThree.PartTwo.KFacts
