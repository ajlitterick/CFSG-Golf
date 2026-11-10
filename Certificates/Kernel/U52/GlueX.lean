module

public import Certificates.Kernel.U52.Bind
public import Certificates.Kernel.U52.ChainX
public import CFSG.Certificates.Kernel.U52.PackEq
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.Misc.ArrBind
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
public import CFSG.Milestones.ASVolI.F48.Rest.Perm
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

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelU52G

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.WordF CFSG.KC.Misc.ArrEnum
  CertificateChecks.KernelU52

theorem rL : ∀ i < 4, Rng 462 9 (LP i) ∧ Rng 462 9 (LPI i) := fun i hi =>
  ⟨fun x hx => (l_range i hi x hx).1, fun x hx => (l_range i hi x hx).2⟩

theorem rE (wd : List (Fin 4 × Bool)) : Rng 462 9 (evFK 462 9 (mask 9) (pidn 462 9) LP LPI wd) :=
  rng_evFK (by norm_num) (by norm_num) (by norm_num) rL wd

theorem cE (wd : List (Fin 4 × Bool)) :
    Canon 462 9 (evFK 462 9 (mask 9) (pidn 462 9) LP LPI wd) :=
  canon_evFK (by norm_num) (by norm_num) (by norm_num) LP LPI wd

theorem rPC {P Q : Nat} (hP : Rng 462 9 P) (hQ : Rng 462 9 Q) :
    Rng 462 9 (pcomp 462 9 (mask 9) P Q) :=
  rng_pcomp (by norm_num) hP hQ

theorem cPC (P Q : Nat) : Canon 462 9 (pcomp 462 9 (mask 9) P Q) :=
  canon_pcomp (by norm_num) (by norm_num) P Q

theorem cId : Canon 462 9 (pidn 462 9) := canon_pidn (by norm_num) (by norm_num)

theorem rId : Rng 462 9 (pidn 462 9) := rng_pidn (by norm_num) (by norm_num)


theorem xPerm : allN 12 (fun j => permOK 462 9 (mask 9) (462 * 9) (CX.S j) (CX.SI j)) = true :=
  (Orb.head_facts CX.head).1

theorem gPerm : ∀ j < 6, permOK 462 9 (mask 9) (462 * 9) (CX.S j) (CX.SI j) = true :=
  fun j hj => allN_spec xPerm j (by omega)

theorem rS : ∀ j < 6, Rng 462 9 (CX.S j) := fun j hj => rng_of_permOK (gPerm j hj)

theorem cS : ∀ j < 6, Canon 462 9 (CX.S j) := fun j hj => canon_of_permOK (gPerm j hj)


end CertificateChecks.KernelU52G

end
