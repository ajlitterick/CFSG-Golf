module

public import CFSG.Open.GriessAllModelsStatement
public import CFSG.Open.GriessG2FourRootInvolutions
import CFSG.RankThree.PerfectCover.HopfCentralCoversUnrestricted
import CFSG.LieType.Simplicity.LieModelFinite
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.LieType.Steinberg.CentralExt.GriessG2FourRootLifts
import CFSG.LieType.Steinberg.CentralExt.GriessCentralCoverRows
import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoMultiplierRow
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

universe u v w

namespace CFSG.Open

open scoped MatrixGroups in
theorem _root_.CFSG.Milestones.cl_lit_griess_schur_multipliers_lie_type
    (p k n : ℕ) [Fact p.Prime] (hk : 0 < k) (hn : 2 ≤ n) (hsmall : n = 2 → 4 ≤ p ^ k) :
    commutator PSL(n, GaloisField p k) = ⊤ ∧
      Nonempty (griessHopfMultiplier PSL(n, GaloisField p k) ≃*
        Multiplicative (ZMod (Nat.gcd n (p ^ k - 1)) ×
          ZMod (griessPSLExceptional n (p ^ k)).1 × ZMod (griessPSLExceptional n (p ^ k)).2)) :=
  CFSG.LieType.Steinberg.CentralExt.SLClosed.griess_psl p k n hk hn hsmall

end CFSG.Open

namespace CFSG.Milestones

open Blueprint.Multiplier CFSG.Open

open CFSG.LieType.Steinberg.CentralExt in
theorem cl_lit_griess_schur_multipliers_all_models
    (X : Type) [Group X] (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ)
    (hmodel : Models.LieModel X t n p f) :
    commutator X = ⊤ ∧
      Nonempty (griessHopfMultiplier X ≃* generic t n p f × exceptional t n p f) :=
  GriessTwistedE6Two.griess_all_models_of_twistedE6_two TwistedE6TwoCover.twistedE6TwoMultiplier
    t n p f hmodel

theorem cl_lit_griess_schur_multipliers_all_models_statement :
    GriessAllModelsStatement :=
  fun X _ t n p f hmodel => cl_lit_griess_schur_multipliers_all_models X t n p f hmodel

theorem cl_lit_griess_schur_multipliers_central_covers
    (X : Type) [Group X] (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ)
    (hmodel : Models.LieModel X t n p f) :
    ((∀ S : Sylow 2 (griessHopfMultiplier X), Nat.card S ≤ 2) →
      ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        ∀ S : Sylow 2 (Subgroup.center L), Nat.card S ≤ 2) ∧
    ((∀ S : Sylow 2 (griessHopfMultiplier X), Nat.card S = 2) →
      ∀ (L L' : Type) [Group L] [Group L'] [Finite L] [Finite L'],
        IsQuasisimple L → IsQuasisimple L' →
        Nat.card (Subgroup.center L) = 2 → Nat.card (Subgroup.center L') = 2 →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        Nonempty ((L' ⧸ Subgroup.center L') ≃* X) → Nonempty (L ≃* L')) := by
  have hquasi (L : Type) [Group L] : Open.IsQuasisimple L ↔ CFSG.IsQuasisimple L :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff L).2.2.1.symm
  simpa only [hquasi] using CFSG.RankThree.PerfectCover.hopf_central_cover_consequences X

theorem cl_lit_griess_schur_multipliers_all_native_models
    (X : Type) [Group X] (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ)
    (hmodel : Blueprint.LieModel X t n p f) :
    commutator X = ⊤ ∧
      Nonempty (griessHopfMultiplier X ≃* generic t n p f × exceptional t n p f) :=
  CFSG.LieType.Steinberg.CentralExt.GriessTwistedE6Two.griess_native_models_of_twistedE6_two
    CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover.twistedE6TwoMultiplier t n p f hmodel


theorem cl_lit_griess_schur_multipliers_central_covers_z2
    (X : Type) [Group X] (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ)
    (hmodel : Models.LieModel X t n p f)
    (ht : t = .PSp ∧ n = 3 ∧ p = 2 ∧ f = 1 ∨ t = .G2 ∧ n = 0 ∧ p = 2 ∧ f = 2 ∨
      t = .F4 ∧ n = 0 ∧ p = 2 ∧ f = 1) :
    Nonempty (griessHopfMultiplier X ≃* Multiplicative (ZMod 2)) ∧
    (∀ (L : Type) [Group L] [Finite L], IsQuasisimple L →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        ∀ S : Sylow 2 (Subgroup.center L), Nat.card S ≤ 2) ∧
    (∀ (L L' : Type) [Group L] [Group L'] [Finite L] [Finite L'],
        IsQuasisimple L → IsQuasisimple L' →
        Nat.card (Subgroup.center L) = 2 → Nat.card (Subgroup.center L') = 2 →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        Nonempty ((L' ⧸ Subgroup.center L') ≃* X) → Nonempty (L ≃* L')) :=
  CFSG.LieType.Steinberg.CentralExt.GriessCentralCovers.central_covers_z2 hmodel ht


end CFSG.Milestones
