module

public import CFSG.Open.StatedDefs
public import CFSG.Open.Defs
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCLin
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCUni
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCSp
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCOrthOdd
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCOrthPlus
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCOrthMinus
import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
import CFSG.Fischer.Uniq.CompTau
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaEven
import CFSG.LieType.Ree.SuzukiSimple
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LieType.Steinberg.Families
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.OddCT
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Structure
import CFSG.LieType.Universal.SpinOmega
import CFSG.LieType.Universal.Unitary
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.KProper
import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoordinateLinear
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneHilbertNinety
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlanePureFieldMatrix
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
import CFSG.RankThree.PartOne.KC.LinearDegreeFive
import CFSG.RankThree.PartOne.KC.LinearSplitInner
import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescent
import CFSG.RankThree.PartOne.KC.SymplecticOrthogonalNoninner
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import CFSG.RankThree.Theta.ThreeComponentOrbitCover
import CFSG.Sporadic.M23.M23Group
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.Open.StatedClassicalModel

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.OFRC (not_dvd_pow_of_ne)

variable {X : Type} [Group X] [Finite X] {n p f r : ℕ}

theorem pRank_psu_eq (h : StatedClassicalModel X .PSU n p f) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrp : r ≠ p) (hdiv : ¬ r ∣ Nat.gcd n (p ^ f + 1)) :
    CFSG.Open.pRank r (⊤ : Subgroup X) =
      if r ∣ p ^ f + 1 then n - 1 else n / orderOf (-((p ^ f : ℕ) : ZMod r)) := by
  obtain ⟨⟨hp, -, hn, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  let : Field K := hfield
  let : Finite K := hfinite
  have hpK : ¬ r ∣ p ^ f := not_dvd_pow_of_ne hr hp hrp.symm
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e,
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pRank_statedProj_SU_formula
      (p := r) (ℓ := p) (n := n) (q := p ^ f) hr hr2 hp ⟨f, rfl⟩ (by omega) hK hpK hdiv]

theorem pRank_psp_eq (h : StatedClassicalModel X .PSp n p f) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrp : r ≠ p) :
    CFSG.Open.pRank r (⊤ : Subgroup X) =
      (if Even (orderOf ((p ^ f : ℕ) : ZMod r)) then 2 * n else n) /
        orderOf ((p ^ f : ℕ) : ZMod r) := by
  obtain ⟨⟨hp, -, hn, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  let : Field K := hfield
  let : Finite K := hfinite
  have hpK : ¬ r ∣ Nat.card K := hK ▸ not_dvd_pow_of_ne hr hp hrp.symm
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e,
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pRank_statedProj_Sp_formula
      (p := r) (n := n) hr hr2 hpK,
    hK]

theorem pRank_pomegaOdd_eq (h : StatedClassicalModel X .POmegaOdd n p f) (hr : r.Prime)
    (hr2 : r ≠ 2) (hrp : r ≠ p) :
    CFSG.Open.pRank r (⊤ : Subgroup X) =
      (if Even (orderOf ((p ^ f : ℕ) : ZMod r)) then 2 * n else n) /
        orderOf ((p ^ f : ℕ) : ZMod r) := by
  obtain ⟨⟨hp, -, hn, hp2⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  let : Field K := hfield
  let : Finite K := hfinite
  have hpK : ¬ r ∣ Nat.card K := hK ▸ not_dvd_pow_of_ne hr hp hrp.symm
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have : Fintype K := Fintype.ofFinite K
  have hF2 : (2 : K) ≠ 0 :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.two_ne_zero_of_odd_card_fintype
      (by rw [← Nat.card_eq_fintype_card]; exact hodd)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e,
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pRank_statedProj_OmegaOdd_formula
      (p := r) (n := n) hr hr2 hn hF2 hpK,
    hK]

theorem pRank_pomegaPlus_eq (h : StatedClassicalModel X .POmegaPlus n p f) (hr : r.Prime)
    (hr2 : r ≠ 2) (hrp : r ≠ p) :
    CFSG.Open.pRank r (⊤ : Subgroup X) =
      if (r : ℤ) ∣ ((p ^ f : ℕ) : ℤ) ^ n + 1 then
        (if Even (orderOf ((p ^ f : ℕ) : ZMod r)) then 2 * (n - 1) else n - 1) /
          orderOf ((p ^ f : ℕ) : ZMod r)
      else (if Even (orderOf ((p ^ f : ℕ) : ZMod r)) then 2 * n else n) /
        orderOf ((p ^ f : ℕ) : ZMod r) := by
  obtain ⟨⟨hp, -, hn⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  let : Field K := hfield
  let : Finite K := hfinite
  have hpK : ¬ r ∣ Nat.card K := hK ▸ not_dvd_pow_of_ne hr hp hrp.symm
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e,
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pRank_statedProj_OmegaPlus_formula
      (p := r) (n := n) hr hr2 hn hpK,
    hK]

theorem pRank_pomegaMinus_eq (h : StatedClassicalModel X .POmegaMinus n p f) (hr : r.Prime)
    (hr2 : r ≠ 2) (hrp : r ≠ p) :
    CFSG.Open.pRank r (⊤ : Subgroup X) =
      if (r : ℤ) ∣ ((p ^ f : ℕ) : ℤ) ^ n - 1 then
        (if Even (orderOf ((p ^ f : ℕ) : ZMod r)) then 2 * (n - 1) else n - 1) /
          orderOf ((p ^ f : ℕ) : ZMod r)
      else (if Even (orderOf ((p ^ f : ℕ) : ZMod r)) then 2 * n else n) /
        orderOf ((p ^ f : ℕ) : ZMod r) := by
  obtain ⟨⟨hp, -, hn⟩, K, hfield, hfinite, hK, b, c, hirr, ⟨e⟩⟩ := h
  let : Field K := hfield
  let : Finite K := hfinite
  have hpK : ¬ r ∣ Nat.card K := hK ▸ not_dvd_pow_of_ne hr hp hrp.symm
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e,
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pRank_statedProj_OmegaMinus_formula
      (p := r) (n := n) hr hr2 hn hirr hpK,
    hK, sub_eq_add_neg]

end CFSG.Open.StatedClassicalModel
