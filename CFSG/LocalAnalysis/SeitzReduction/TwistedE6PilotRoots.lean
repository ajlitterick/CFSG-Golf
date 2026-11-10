module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAmalgam
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassListBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassesReps
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
public import CFSG.LieType.Chevalley.GraphFixedF4Intertwiner
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEInner
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

local instance twistedE6PilotRootsNeZeroE6 : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

local instance twistedE6PilotRootsNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance twistedE6PilotRootsNeZeroFolded : NeZero TwistTag.E6.foldedTag.rank := ⟨by decide⟩

local notation "ρ" => permLattice TwistTag.E6.perm


theorem mem_orbit_f4FoldedIndex_iff (i : Fin TwistTag.E6.tag.rank) (a : Fin Tag.F4.rank) :
    i ∈ TwistTag.E6.orbit (f4FoldedIndex a) ↔ e6IndexToF4 i = a := by
  revert i a
  decide

theorem e6ToF4_apply_eq_sum (γ : Fin TwistTag.E6.tag.rank → ℤ) (a : Fin Tag.F4.rank) :
    e6ToF4 γ a = ∑ i ∈ TwistTag.E6.orbit (f4FoldedIndex a), γ i := by
  fin_cases a
  · change γ 1 = ∑ i ∈ ({1} : Finset (Fin TwistTag.E6.tag.rank)), γ i
    rw [Finset.sum_singleton]
  · change γ 3 = ∑ i ∈ ({3} : Finset (Fin TwistTag.E6.tag.rank)), γ i
    rw [Finset.sum_singleton]
  · change γ 2 + γ 4 = ∑ i ∈ ({2, 4} : Finset (Fin TwistTag.E6.tag.rank)), γ i
    rw [Finset.sum_pair (by decide)]
  · change γ 0 + γ 5 = ∑ i ∈ ({0, 5} : Finset (Fin TwistTag.E6.tag.rank)), γ i
    rw [Finset.sum_pair (by decide)]


theorem e6ToF4_check : ∀ γ ∈ rootFinset TwistTag.E6.tag,
    (ρ γ = γ ↔ iform (e6ToF4 γ) (e6ToF4 γ) = 4) ∧ (ρ γ ≠ γ → iform γ (ρ γ) = 0) := by
  decide +kernel


section RelativeRoots

variable {γ : Fin TwistTag.E6.tag.rank → ℤ}


theorem iform_permLattice_eq_zero (hγ : IsRoot TwistTag.E6.tag γ) (h : ρ γ ≠ γ) :
    iform γ (ρ γ) = 0 :=
  (e6ToF4_check γ (mem_rootFinset.2 hγ)).2 h

end RelativeRoots


theorem d4Perp_check :
    (∀ δ ∈ rootFinset TwistTag.E6.tag, ¬ (iform δ (Pi.single 1 1) = 0 ∧
      iform δ (Pi.single 2 1) = 0 ∧ iform δ (Pi.single 3 1) = 0 ∧
        iform δ (Pi.single 4 1) = 0)) ∧
      ((rootFinset TwistTag.E6.tag).filter fun δ => δ 0 = 0 ∧ δ 5 = 0).card = 24 := by
  decide +kernel


@[expose] def rootE15 : Fin TwistTag.E6.tag.rank → ℤ := ![1, 0, 1, 1, 1, 0]

@[expose] def rootE26 : Fin TwistTag.E6.tag.rank → ℤ := ![0, 0, 1, 1, 1, 1]

@[expose] def relRoot0121 : Fin Tag.F4.rank → ℤ := ![0, 1, 2, 1]

theorem repRoots_check :
    (ρ (Pi.single 3 1) = Pi.single 3 1 ∧
        iform (Pi.single 3 1 : Fin TwistTag.E6.tag.rank → ℤ) e6HighestRoot = 0 ∧
        rootE15 ∈ rootFinset TwistTag.E6.tag ∧ ρ rootE15 = rootE26 ∧
        iform rootE15 rootE26 = 0 ∧ rootE15 1 = 0 ∧ rootE26 1 = 0 ∧
        e6ToF4 rootE15 = relRoot0121 ∧ iform F4Pilot.rootR (e6ToF4 rootE15) = 0) ∧
      (ρ (Pi.single 1 1) = Pi.single 1 1 ∧
        iform (Pi.single 1 1 : Fin TwistTag.E6.tag.rank → ℤ) twistedE6ClassRootU = 0 ∧
        iform (Pi.single 1 1 : Fin TwistTag.E6.tag.rank → ℤ) twistedE6ClassRootU' = 0 ∧
        ρ (Pi.single 2 1) = Pi.single 4 1 ∧
        iform (Pi.single 2 1 : Fin TwistTag.E6.tag.rank → ℤ) (Pi.single 4 1) = 0 ∧
        iform (Pi.single 2 1 : Fin TwistTag.E6.tag.rank → ℤ) twistedE6ClassRootU +
          iform (Pi.single 2 1 : Fin TwistTag.E6.tag.rank → ℤ) twistedE6ClassRootU' = 0 ∧
        e6ToF4 (Pi.single 2 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single 2 1 ∧
        iform F4Pilot.rootS (e6ToF4 (Pi.single 2 1 : Fin TwistTag.E6.tag.rank → ℤ)) = 0) := by
  decide +kernel

theorem isRoot_rootE15 :
    IsRoot TwistTag.E6.tag rootE15 ∧ IsRoot TwistTag.E6.tag rootE26 := by
  have h : rootE15 ∈ rootFinset TwistTag.E6.tag ∧ rootE26 ∈ rootFinset TwistTag.E6.tag := by
    decide +kernel
  exact ⟨mem_rootFinset.1 h.1, mem_rootFinset.1 h.2⟩

@[expose] def relWordTX : List (Fin TwistTag.E6.foldedTag.rank) := [3, 1, 2, 0, 1, 2, 3]

@[expose] def relWordTY : List (Fin TwistTag.E6.foldedTag.rank) := [2, 1, 2, 0, 1, 2, 3]

@[expose] def relWordUX : List (Fin TwistTag.E6.foldedTag.rank) := [3, 2, 0, 1, 0]

@[expose] def relWordUY : List (Fin TwistTag.E6.foldedTag.rank) := [2, 3, 0, 1, 2, 0, 1, 0]

@[expose] def relWordXPrime : List (Fin TwistTag.E6.foldedTag.rank) := [2, 3]

theorem relWords_check :
    twistedE6RelAct relWordTX e6HighestRoot = Pi.single 3 1 ∧
      twistedE6RelAct relWordTY e6HighestRoot = Pi.single 1 1 ∧
      twistedE6RelAct relWordUX twistedE6ClassRootU = rootE15 ∧
      twistedE6RelAct relWordUX twistedE6ClassRootU' = rootE26 ∧
      twistedE6RelAct relWordUY twistedE6ClassRootU = Pi.single 2 1 ∧
      twistedE6RelAct relWordUY twistedE6ClassRootU' = Pi.single 4 1 ∧
      twistedE6RelAct relWordXPrime e6HighestRoot = twistedE6ClassRootB := by
  decide +kernel

theorem conj_mul_distrib {M : Type*} [Group M] (n a b : M) :
    n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := by
  group

section Transport

variable {K : Type} [Field K] [CharP K 2]

theorem conj_relWordTX_pinnedX_highRoot (c : K) :
    twistedE6RelWeyl K relWordTX * pinnedX TwistTag.E6.tag K e6HighestRoot c *
        (twistedE6RelWeyl K relWordTX)⁻¹ = pinnedX TwistTag.E6.tag K (Pi.single 3 1) c := by
  rw [twistedE6RelWeyl_conj_pinnedX relWordTX isRoot_e6HighestRoot c, relWords_check.1]

theorem conj_relWordTY_pinnedX_highRoot (c : K) :
    twistedE6RelWeyl K relWordTY * pinnedX TwistTag.E6.tag K e6HighestRoot c *
        (twistedE6RelWeyl K relWordTY)⁻¹ = pinnedX TwistTag.E6.tag K (Pi.single 1 1) c := by
  rw [twistedE6RelWeyl_conj_pinnedX relWordTY isRoot_e6HighestRoot c, relWords_check.2.1]

theorem conj_relWordUX_twistedE6ClassU :
    twistedE6RelWeyl K relWordUX * twistedE6ClassU K * (twistedE6RelWeyl K relWordUX)⁻¹ =
      pinnedX TwistTag.E6.tag K rootE15 1 * pinnedX TwistTag.E6.tag K rootE26 1 := by
  rw [twistedE6ClassU, conj_mul_distrib,
    twistedE6RelWeyl_conj_pinnedX relWordUX isRoot_twistedE6ClassRoots.1,
    twistedE6RelWeyl_conj_pinnedX relWordUX isRoot_twistedE6ClassRoots.2.1,
    relWords_check.2.2.1, relWords_check.2.2.2.1]

theorem conj_relWordUY_twistedE6ClassU :
    twistedE6RelWeyl K relWordUY * twistedE6ClassU K * (twistedE6RelWeyl K relWordUY)⁻¹ =
      pinnedX TwistTag.E6.tag K (Pi.single 2 1) 1 *
        pinnedX TwistTag.E6.tag K (Pi.single 4 1) 1 := by
  rw [twistedE6ClassU, conj_mul_distrib,
    twistedE6RelWeyl_conj_pinnedX relWordUY isRoot_twistedE6ClassRoots.1,
    twistedE6RelWeyl_conj_pinnedX relWordUY isRoot_twistedE6ClassRoots.2.1,
    relWords_check.2.2.2.2.1, relWords_check.2.2.2.2.2.1]


end Transport

end CFSG.SeitzReduction.TwistedE6Pilot
