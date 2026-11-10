module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150SporCore
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzA
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzB
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThShapeZ
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp2
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporThCent
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47LThree
public import CFSG.RankThree.PartTwo.Sec4.Item47SpFour
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.Presentation.ThBase
public import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.GH74.GLS.Balance.SolvAPIDefs
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCentU
import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
import CFSG.RankThree.PartTwo.Sec11.Item119K
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
import CFSG.RankThree.PartTwo.Sec20.OneSteps
import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem k150s_forall_goodFor_of_mulEquiv {J : Type} [Group J] {T T' : Type} [Group T]
    [Group T'] (e : T ≃* T')
    (h : ∀ x : T', orderOf x = 3 → GoodFor J (Subgroup.centralizer ({x} : Set T'))) :
    ∀ x : T, orderOf x = 3 → GoodFor J (Subgroup.centralizer ({x} : Set T)) := fun x hx =>
  k150s_goodFor_of_mulEquiv_centralizer e (h (e x) (by rwa [MulEquiv.orderOf_eq]))

section Suz

open CFSG.HardMathSupport.Dickson.I271 (fuseXA fuseXB fuseXA_pow fuseXA_ne_one fuseXB_pow
  suz_exists_conj_classes aSub aSub_eq aSub_le aSub_quasisimple aX_mem)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT (yPerm yPerm_pow Cy_eq)
open CFSG.Sporadic.SuzOddCore (suzM suzEquivM suzM_card)


private theorem k150s_goodFor_suz_A {J : Type} [Group J] (hJ : K150sTgt J) :
    GoodFor J (Subgroup.centralizer ({fuseXA} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  have := hJ.simple.toNontrivial
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← aSub_eq]
  refine k150s_goodFor_of_isQuasisimple_of_central
    (RonanK429H.isQuasisimple_of_open aSub_quasisimple.1) aX_mem
    (orderOf_eq_prime fuseXA_pow fuseXA_ne_one) fun g hg => ?_
  exact Subgroup.mem_centralizer_singleton_iff.1 (aSub_le hg).1

private theorem k150s_goodFor_suz_B {J : Type} [Group J] (hJ : K150sTgt J) :
    GoodFor J (Subgroup.centralizer ({fuseXB} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  obtain ⟨hcard, -, hle, hnorm, -⟩ := CFSG.HardMathSupport.Dickson.I271.TabSuzB.caseB_spec
  refine k150s_goodFor_of_normal_three hle hnorm
    (IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)) hJ.simple hJ.not_isPGroup
    (M := Nat.card suzM) (Subgroup.card_dvd_of_le inf_le_right) ?_
  rw [hcard, suzM_card]
  rcases hJ.card with hc | hc <;> rw [hc] <;> norm_num

private theorem k150s_goodFor_suz_C {J : Type} [Group J] (hJ : K150sTgt J) :
    GoodFor J (Subgroup.centralizer ({yPerm} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  obtain ⟨hCeq, hcard⟩ := Cy_eq
  have h3240 : Nat.card ↥(Subgroup.centralizer ({yPerm} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) =
      3240 := by
    rw [← hCeq]
    exact hcard
  exact k150s_goodFor_of_not_dvd (hJ.not_dvd (by rw [h3240]; norm_num) (by rw [h3240]; norm_num))


private theorem k150s_goodFor_suz {J : Type} [Group J] (hJ : K150sTgt J)
    (x : Equiv.Perm (Fin 1782)) (hx : x ∈ suzM) (hxo : orderOf x = 3) :
    GoodFor J (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  obtain ⟨k, hk, c, hc, e, he, rfl⟩ := suz_exists_conj_classes hx hxo
  rcases hc with rfl | rfl | rfl
  · exact k150s_goodFor_conj hk fuseXA_pow he (k150s_goodFor_suz_A hJ)
  · exact k150s_goodFor_conj hk fuseXB_pow he (k150s_goodFor_suz_B hJ)
  · exact k150s_goodFor_conj hk yPerm_pow he (k150s_goodFor_suz_C hJ)


private theorem k150s_noCfg_suz {J : Type} [Group J] (hJ : K150sTgt J) :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .Suz) → NoCfgFor J S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Suz)) := by
    rw [CFSG.Sporadic.SuzOddCore.outer_carrier_suz.1]
    norm_num
  exact k150s_noCfg_of_subgroupModel (e.trans suzEquivM)
    (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (RonanK429H.not_three_dvd_outer_of_mulEquiv e hout) (k150s_goodFor_suz hJ)


theorem k150s_suz {J : Type} [Group J] (hJ : K150sTgt J) : RowOfK150 J (Spor .Suz) :=
  k150s_row_of_native (s := .Suz) CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv (k150s_noCfg_suz hJ)

end Suz

section Th

open CFSG.Sporadic.Th (thEquivJ)
open CFSG.HardMathSupport.Dickson.I271 (thS thZ thU th_census th_orderOf card_centralizer_zJ_dvd
  thEps th_letters_spec leaf_closure_of_six normal_of_simple_not_dvd_factorial)
open CFSG.GH74.QTGen4.Recog.G23 (SatisfiesG23Words)
open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest (lift_mk_eq_evalW)

private theorem k150s_goodFor_of_simple_g23 {J : Type} [Group J] (hJ : K150sTgt J) {Q : Type}
    [Group Q] [Finite Q] {C E : Subgroup Q} (hEC : E ≤ C) (hs : IsSimpleGroup ↥E)
    (hcard : Nat.card E = 4245696) (hC : Nat.card C ≤ 63685439) : GoodFor J C := by
  set E' : Subgroup C := E.subgroupOf C with hE'
  have eE : ↥E' ≃* ↥E := Subgroup.subgroupOfEquivOfLe hEC
  have : IsSimpleGroup ↥E' := MulEquiv.isSimpleGroup eE
  have hcardE' : Nat.card E' = 4245696 := (Nat.card_congr eE.toEquiv).trans hcard
  have hidx : E'.index ≤ 14 := by
    have h1 := Subgroup.index_mul_card E'
    rw [hcardE'] at h1
    by_contra h
    have : 15 ≤ E'.index := by omega
    omega
  have hnd : ∀ n ≤ 14, ¬ 4245696 ∣ n.factorial := by
    intro n hn
    interval_cases n <;> decide
  have hnormE' : E'.Normal := by
    refine normal_of_simple_not_dvd_factorial E' ?_
    rw [hcardE']
    exact hnd _ hidx
  refine k150s_goodFor_of_simple_normal hEC hnormE' hs ?_ ?_
  · rw [hcard]
    have h2520 : 2520 ≤ Nat.card J := by
      rcases hJ.card with hc | hc <;> omega
    have := Nat.mul_le_mul_right 4245696 h2520
    omega
  · rw [hcard]
    rcases hJ.card with hc | hc <;> rw [hc] <;> norm_num


private theorem k150s_goodFor_thZ {J : Type} [Group J] (hJ : K150sTgt J) :
    GoodFor J (Subgroup.centralizer ({thZ} : Set ↥CFSG.Sporadic.Th.J)) :=
  k150s_goodFor_of_card_dvd (M := 2 ^ 3 * 3 ^ 10) card_centralizer_zJ_dvd
    (hJ.not_dvd (by norm_num) (by norm_num))

private theorem k150s_goodFor_thU {J : Type} [Group J] (hJ : K150sTgt J) :
    GoodFor J (Subgroup.centralizer ({thU} : Set ↥CFSG.Sporadic.Th.J)) :=
  k150s_goodFor_of_not_dvd (hJ.not_dvd
    (by rw [CFSG.RankThree.PartTwo.Sec4.RonanK432.th_card_centralizer_U]; norm_num)
    (by rw [CFSG.RankThree.PartTwo.Sec4.RonanK432.th_card_centralizer_U]; norm_num))

private theorem k150s_goodFor_thS {J : Type} [Group J] (hJ : K150sTgt J) :
    GoodFor J (Subgroup.centralizer ({thS} : Set ↥CFSG.Sporadic.Th.J)) := by
  have : Finite ↥CFSG.Sporadic.Th.J :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.finite_J
  obtain ⟨hrel, hcomm, hne⟩ := th_letters_spec
  have hε : SatisfiesG23Words thEps := fun r hr => (lift_mk_eq_evalW _ r).trans (hrel r hr)
  obtain ⟨-, hsimp, -, hcard⟩ := leaf_closure_of_six thEps hε hne
  have hEC : Subgroup.closure (Set.range thEps) ≤
      Subgroup.centralizer ({thS} : Set ↥CFSG.Sporadic.Th.J) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm i).symm
  exact k150s_goodFor_of_simple_g23 hJ hEC hsimp hcard
    CFSG.HardMathSupport.Dickson.Sec6.th3_facts.2.2.2.2.2


private theorem k150s_goodFor_thJ {J : Type} [Group J] (hJ : K150sTgt J) (x : ↥CFSG.Sporadic.Th.J)
    (hx : orderOf x = 3) :
    GoodFor J (Subgroup.centralizer ({x} : Set ↥CFSG.Sporadic.Th.J)) := by
  obtain ⟨k, c, hc, e, he, rfl⟩ := th_census x hx
  obtain ⟨hs, hz, hu⟩ := th_orderOf
  have hg : GoodFor J (Subgroup.centralizer ({c} : Set ↥CFSG.Sporadic.Th.J)) ∧ c ^ 3 = 1 := by
    rcases hc with rfl | rfl | rfl
    · exact ⟨k150s_goodFor_thS hJ, by rw [← hs]; exact pow_orderOf_eq_one _⟩
    · exact ⟨k150s_goodFor_thZ hJ, by rw [← hz]; exact pow_orderOf_eq_one _⟩
    · exact ⟨k150s_goodFor_thU hJ, by rw [← hu]; exact pow_orderOf_eq_one _⟩
  have ha : GoodFor J (Subgroup.centralizer ({c ^ e} : Set ↥CFSG.Sporadic.Th.J)) := by
    rw [RonanK429H.centralizer_pow_of_pow_three hg.2 he]
    exact hg.1
  exact k150s_goodFor_of_isConj (isConj_iff.mpr ⟨k, rfl⟩) ha


private theorem k150s_noCfg_th {J : Type} [Group J] (hJ : K150sTgt J) :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .Th) → NoCfgFor J S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Th)) := by
    rw [show Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Th)) = 1 from
      CFSG.RankThree.PartOne.SPOR.card_outer_Th_native]
    norm_num
  have hnat : ∀ x : Blueprint.NativeSporadic.Th, orderOf x = 3 →
      GoodFor J (Subgroup.centralizer ({x} : Set Blueprint.NativeSporadic.Th)) :=
    @k150s_forall_goodFor_of_mulEquiv J _ Blueprint.NativeSporadic.Th ↥CFSG.Sporadic.Th.J
      Units.instGroup _ thEquivJ (k150s_goodFor_thJ hJ)
  exact k150s_noCfg_of_model (G' := Blueprint.NativeSporadic.Th) e
    (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (RonanK429H.not_three_dvd_outer_of_mulEquiv e hout) hnat


theorem k150s_th {J : Type} [Group J] (hJ : K150sTgt J) : RowOfK150 J (Spor .Th) :=
  k150s_row_of_native (s := .Th) CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv (k150s_noCfg_th hJ)

end Th

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150
