module

public import Certificates.Certificate7767
public import Certificates.Certificate7768
public import Certificates.Certificate7769
public import CFSG.Milestones.ASVolI.F48.Rest.Perm
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphisms
public import CFSG.ClassicalGroups
public import CFSG.GH74.Statements
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Cfg4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InPartI2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Milestones.ASVolI.F48.Rest.Eng
public import CFSG.Milestones.ASVolI.F48.Small.Base
public import CFSG.Milestones.ASVolI.F4Native
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Recognition.CertTwoLocalPair
public import CFSG.Quasithin.Recognition.CertU33Wreath
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2RootRel
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStd
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Thm
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisNormalizers
public import CFSG.Sporadic.Schreier.J4SSylow
public import Certificates.Kernel.J4Count.FixCE

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates

attribute [local irreducible] burnsideF48t_u52LArr burnsideF48t_u52GensArr

theorem burnsideF48t_u52_nodupP1 : burnsideF48t_u52BaseP1.Nodup := by decide
theorem burnsideF48t_u52_nodupP2 : burnsideF48t_u52BaseP2.Nodup := by decide
theorem burnsideF48t_u52_nodupB : burnsideF48t_u52BaseB.Nodup := by decide
theorem burnsideF48t_u52_nodupK : burnsideF48t_u52BaseK.Nodup := by decide


@[expose] def burnsideF48t_u52P1' : Subgroup (Equiv.Perm (Fin 462)) :=
  arrGen 462 burnsideF48t_u52P1Arr

@[expose] def burnsideF48t_u52P2' : Subgroup (Equiv.Perm (Fin 462)) :=
  arrGen 462 burnsideF48t_u52P2Arr

@[expose] def burnsideF48t_u52B' : Subgroup (Equiv.Perm (Fin 462)) :=
  arrGen 462 burnsideF48t_u52BArr

@[expose] def burnsideF48t_u52S0' : Subgroup (Equiv.Perm (Fin 462)) :=
  arrGen 462 (burnsideF48t_u52S0Arr ())

@[expose] def burnsideF48t_u52K' : Subgroup (Equiv.Perm (Fin 462)) :=
  arrGen 462 (burnsideF48t_u52KArr ())

section Chains

theorem burnsideF48t_u52_chains : burnsideF48t_u52ChainXOK () = true ∧
    burnsideF48t_u52ChainP1OK () = true ∧ burnsideF48t_u52ChainP2OK () = true ∧
    burnsideF48t_u52ChainBOK () = true ∧ burnsideF48t_u52ChainS0OK () = true ∧
    burnsideF48t_u52ChainKOK () = true :=
  Certificates.certificate7767


theorem burnsideF48t_u52_card_P1' : Nat.card ↥burnsideF48t_u52P1' = 82944 := by
  rw [burnsideF48t_u52P1', card_arrGen_of_chainCheck (by norm_num) burnsideF48t_u52_nodupP1
    burnsideF48t_u52_chains.2.1]
  rfl

theorem burnsideF48t_u52_card_P2' : Nat.card ↥burnsideF48t_u52P2' = 46080 := by
  rw [burnsideF48t_u52P2', card_arrGen_of_chainCheck (by norm_num) burnsideF48t_u52_nodupP2
    burnsideF48t_u52_chains.2.2.1]
  rfl

theorem burnsideF48t_u52_card_B' : Nat.card ↥burnsideF48t_u52B' = 9216 := by
  rw [burnsideF48t_u52B', card_arrGen_of_chainCheck (by norm_num) burnsideF48t_u52_nodupB
    burnsideF48t_u52_chains.2.2.2.1]
  rfl


theorem burnsideF48t_u52_card_K' : Nat.card ↥burnsideF48t_u52K' = 9 := by
  rw [burnsideF48t_u52K', card_arrGen_of_chainCheck (by norm_num) burnsideF48t_u52_nodupK
    burnsideF48t_u52_chains.2.2.2.2.2]
  rfl


end Chains

section Letters


@[expose] noncomputable def burnsideF48t_u52σ (i : ℕ) : Equiv.Perm (Fin 462) :=
  CFSG.ONSchreier.permOfArr 462 burnsideF48t_u52LArr[i]!


end Letters

section Stab


end Stab

end CFSG.ASVolI
