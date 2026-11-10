
module

public import CFSG.Quasithin.Recognition.RuRank3J55DataInputs
public import Certificates.Kernel.SporSch.Ru.Q7307K
import Certificates.Kernel.SporSch.Ru.Iso7047
import Certificates.Kernel.SporSch.Ru.G2Ru7164
import Certificates.Kernel.SporSch.Tits.Graph2265N
import CFSG.Certificates.Kernel.SporSch.OrbLabelsSound
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Q7307

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.OrbLab
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.G2Ru7164
  CFSG.Quasithin.RuRank3 CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits CFSG.KC.BfsPin

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem nat_beq (a b : Nat) : (a == b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

theorem qlab_get {y : Nat} (hy : y < 4060) : ruQLab[y]! = Lf y := by
  have hs : ruR0Arrs.size = 4 := by simp [ruR0Arrs]
  have hg : ∀ k < 4, ∀ x < 4060, ga ruR0Arrs k x = gR k x := fun k hk x hx => by
    unfold ga ruR0Arrs
    rw [getElem!_ofFn_of_lt _ hk]
    change (ruR0Arr k)[x]! = _
    rw [Iso7047.r_eq hk, CFSG.KC.BfsPin.unpack_get' hx]
    rfl
  exact (orbLabels_of_K hs hg kOrb).2 y hy

theorem ti_eq : ruTI1 = unpack 4060 12 TI := by
  have hP : ∀ j < 2, P (Af j) := fun j hj => by
    interval_cases j
    · exact PP_of_permOK hsz kPerm0
    · exact PP_of_permOK hsz kPerm1
  have hS : ∀ j < 2, ruGensA[j]! = unpack 4060 12 (Af j) := fun j hj => by
    interval_cases j
    · rw [show ruGensA[0]! = ruA0A by simp [ruGensA], a0_eq]
      rfl
    · rw [show ruGensA[1]! = ruA1A by simp [ruGensA], a1_eq]
      rfl
  have hinv : ruGensInvA = ruGensA.map (invCand 4060) := by
    simp [ruGensInvA, ruGensA, ruInv]
  have hw : ∀ l ∈ Iso7047.twK 32 1, l ≠ 0 ∧ l.natAbs ≤ 2 := fun l hl => by
    have := List.all_eq_true.1 kWord l hl
    simpa using this
  have e : ruTreeWord 1 = Iso7047.twK 32 1 := Iso7047.treeWordAux_eq 32 1 (by norm_num)
  obtain ⟨h1, h2⟩ := wordA_eq (S := ruGensA) (k := 2) (by simp [ruGensA]) hS hP _ hw
  change invCand 4060 (wordA 4060 ruGensA ruGensInvA (ruTreeWord 1)) = _
  rw [hinv, e, h1, inv_eq h2]
  rfl


end CertificateChecks.KernelSporSch.Q7307

end
