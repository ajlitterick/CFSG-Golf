module

public import CFSG.LocalAnalysis.StandardType.GGLangRatCompTorusLift
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacE
import CFSG.LocalAnalysis.StandardType.GGCompFieldLieModel
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
import CFSG.ClassicalInvolution.Q3.Q3TWWMinus
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4All
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
import CFSG.RankThree.PartOne.KEXC.Basic
import CFSG.RankThree.PartOne.TCX.Ree.Perm

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw

theorem langRatField_outerE
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hE : 6 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    GGCompFieldAt (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hq' : CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hℓp : ringChar L ≠ p := by
    rw [ringChar.eq L 2]
    exact fun h => hp2 h.symm
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hm : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    S.componentOrbitLength_eq_one_of_five_leT hT i (by have := hE.1; omega)
  have h2 : ringChar L = 2 := ringChar.eq L 2
  rcases hτ with rfl | rfl
  · obtain ⟨f, -, hqe, hlie⟩ :=
      lieModel_rationalComponent_of_outer_E7 S hp hpL hT hTp i hE.1 hE.2 hout
    rw [h2] at hlie hqe
    rw [hm, pow_one, ← hqe]
    exact CFSG.StandardType.ggCompFieldAt_of_lieModel hq' hlie ⟨by decide, by decide, by decide⟩
  · obtain ⟨f, -, hqe, hlie⟩ :=
      lieModel_rationalComponent_of_outer_E8 S hp hpL hT hTp i hE.1 hE.2 hout
    rw [h2] at hlie hqe
    rw [hm, pow_one, ← hqe]
    exact CFSG.StandardType.ggCompFieldAt_of_lieModel hq' hlie ⟨by decide, by decide, by decide⟩

theorem langRatField_outerD_high
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hD : 5 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    GGCompFieldAt (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hq' : CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hm : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    S.componentOrbitLength_eq_one_of_five_leT hT i hD.1
  have h2 : ringChar L = 2 := ringChar.eq L 2
  obtain ⟨m, e, hqe, hlie⟩ := lieModel_rationalComponent_of_twoD_highG hp S hT hap h1 i hD.1 hD.2
    hout (fun _ _ => True)
    (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega)) trivial
  rw [h2] at hlie hqe
  rw [hm, pow_one, ← hqe]
  exact CFSG.StandardType.ggCompFieldAt_of_lieModel hq' hlie ⟨by decide, by decide, by decide⟩

end CFSG.StandardType.LangRat
