module

public import Certificates.Kernel.B45.C260394V0
public import Certificates.Kernel.B45.C260394V1
public import Certificates.Kernel.B45.C260394T0
public import Certificates.Kernel.B45.C260394T1
public import Certificates.Kernel.B45.C260394T2
public import Certificates.Kernel.Misc.RuSq.Bind
public import CFSG.Certificates.Kernel.B45RuSylSound
public import CFSG.Sporadic.Schreier.RuSEnum
import CFSG.Certificates.Kernel.Misc.RuInvCov
import CFSG.Certificates.Kernel.Misc.RuInvSound
import Certificates.Kernel.Sporadic.ON.Gen
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Sporadic.Schreier.RuSylow
public import CFSG.Sporadic.Schreier.RuTreeElt
public import CFSG.Sporadic.Schreier.RuWitReps
import CFSG.Certificates.Kernel.Misc.RuInvHash
import CFSG.Certificates.Kernel.Spor.ClassOneH

public section

set_option Elab.async false

#kon_join CertificateChecks.KernelB45.C260394.covAll CertificateChecks.KernelB45.C260394.covB 64
#kon_join CertificateChecks.KernelB45.C260394.rowAll CertificateChecks.KernelB45.C260394.rowB 33

namespace CertificateChecks.KernelB45.C260394

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B45P.RuSyl CFSG.KC.B45P.RuSylS
  CertificateChecks.KernelMisc CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native CFSG.Quasithin.B45Exc.Tab
  CFSG.KS.Raw.Orb CFSG.Certificates.ChainArrays

theorem cnt : (Nat.beq (rcnt (RuSqS.LR 0)) 2048 && Nat.beq (rcnt (RuSqS.LR 1)) 8) = true := by
  quickRfl

theorem hc : rcnt (RuSqS.LR 0) = 2048 ∧ rcnt (RuSqS.LR 1) = 8 := by
  have h := cnt
  rw [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

noncomputable abbrev lT (i k : Nat) : Equiv.Perm (Fin 4060) :=
  levT 4060 (ruField4060 4) (ruBaseArr 4060 ruS4060ChainBase) i k

theorem lev_size (i : Nat) (hi : i < 2) :
    (lev 4060 (ruField4060 4) (ruBaseArr 4060 ruS4060ChainBase) i).pts.size = rcnt (RuSqS.LR i) :=
  (CFSG.KC.Misc.RuInv.P.lev2 RuSq.bindsSq RuSq.permS RuSqS.hl hi).1


theorem hA : ChainArrays ruChainS4060 ((ruField4060 4).extract 0 4) (ruField4060 4)
    (ruBaseArr 4060 ruS4060ChainBase) (ruWordsArr 4 6 ruS4060ChainDerivations) :=
  ruChain_arrays ruInv_check.1

theorem hT {i k : Nat} (hi : i < 2) (hk : k < rcnt (RuSqS.LR i)) :
    PRep 4060 12 (RuSqS.TR (Nat.add (roff 4060 48720 (RuSqS.LR i)) k)) (lT i k) := by
  obtain ⟨g, hr, hp⟩ := (CFSG.KC.Misc.RuInv.P.lev2 RuSq.bindsSq RuSq.permS RuSqS.hl hi).2 k hk
  have h := ruInv_check.1
  have hr' := hA.rep_levT (chainCheckFacts h) (i := i) (k := k)
    (by change i < 2; exact hi) (by rw [lev_size i hi]; exact hk)
  have e : lT i k = g := hr'.unique hr
  rw [e]
  exact hp

theorem hgen' {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruChainS4060.originalSubgroup) :
    ∃ a < 2048, ∃ b < 8, g = lT 0 a * lT 1 b := by
  have h := ruInv_check.1
  obtain ⟨a, ha, b, hb, e⟩ := chain_exists_prod2 hA (by norm_num : 0 < 4) h
    (by change 2 ≤ 2; exact le_rfl) (fun i h1 h2 => by change i < 2 at h2; omega) hg
  rw [lev_size 0 (by norm_num), hc.1] at ha
  rw [lev_size 1 (by norm_num), hc.2] at hb
  exact ⟨a, ha, b, hb, e.symm⟩

theorem hin' {a b : Nat} (ha : a < 2048) (hb : b < 8) :
    lT 0 a * lT 1 b ∈ ruChainS4060.originalSubgroup := by
  have h := ruInv_check.1
  exact Subgroup.mul_mem _
    (chain_levT_mem_original hA (by norm_num : 0 < 4) h
      (by change 0 < 2; norm_num) (by rw [lev_size 0 (by norm_num), hc.1]; exact ha))
    (chain_levT_mem_original hA (by norm_num : 0 < 4) h
      (by change 1 < 2; norm_num) (by rw [lev_size 1 (by norm_num), hc.2]; exact hb))

theorem hcov : ∀ c < 16384, covC (RuSqS.LR 0) (RuSqS.LR 1) RuSqS.TR RuSqS.TRI CD IX
    (roff 4060 48720 (RuSqS.LR 0)) (roff 4060 48720 (RuSqS.LR 1)) c = true := by
  have h := CFSG.KC.Misc.RuInv.forall_of_blocks (K := 256) (Q := 64)
    (f := covC (RuSqS.LR 0) (RuSqS.LR 1) RuSqS.TR RuSqS.TRI CD IX
      (roff 4060 48720 (RuSqS.LR 0)) (roff 4060 48720 (RuSqS.LR 1))) fun q hq => by
    have e := covAll q hq
    unfold covB at e
    rwa [CFSG.KC.B45P.RuSylS.strictB_eq, CFSG.KC.B45P.RuSylS.strictB_eq, CFSG.KC.B45P.RuSylS.strictB_eq, CFSG.KC.B45P.RuSylS.strictB_eq] at e
  exact fun c hc => h c (by omega)

theorem hinv : ∀ i < 495, invC RuSqS.TR CD IX K0 K1 (roff 4060 48720 (RuSqS.LR 0))
    (roff 4060 48720 (RuSqS.LR 1)) i = true := by
  have e := invOK
  unfold invB at e
  rw [CFSG.KC.B45P.RuSylS.strictB_eq, CFSG.KC.B45P.RuSylS.strictB_eq] at e
  exact CFSG.KS.allN_spec e

theorem hrow : ∀ i < 495, rowC RuSqS.TR CD K0 K1 CM PR (roff 4060 48720 (RuSqS.LR 0))
    (roff 4060 48720 (RuSqS.LR 1)) i = true := by
  have h := CFSG.KC.Misc.RuInv.forall_of_blocks (K := 15) (Q := 33)
    (f := rowC RuSqS.TR CD K0 K1 CM PR (roff 4060 48720 (RuSqS.LR 0))
      (roff 4060 48720 (RuSqS.LR 1))) fun q hq => by
    have e := rowAll q hq
    unfold rowB at e
    rwa [CFSG.KC.B45P.RuSylS.strictB_eq, CFSG.KC.B45P.RuSylS.strictB_eq] at e
  exact fun i hi => h i (by omega)

theorem hk : K0 495 = 0 ∧ K1 495 = 1 := by
  have h := k495
  rw [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩


end CertificateChecks.KernelB45.C260394

end
