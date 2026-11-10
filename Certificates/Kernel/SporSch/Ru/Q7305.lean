
module

public import Certificates.Kernel.SporSch.Ru.Q7305K
import Certificates.Kernel.SporSch.Ru.Q7307
import Certificates.Kernel.SporSch.Ru.Iso7047
import Certificates.Kernel.SporSch.Ru.G2Ru7164
import Certificates.Kernel.SporSch.Ru.JFacts
import CFSG.Certificates.Kernel.SporSch.OrbLabelsSound
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Q7305

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.OrbLab
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.G2Ru7164
  CertificateChecks.KernelSporSch.Q7307
  CFSG.Quasithin.RuRank3 CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits CFSG.KC.BfsPin

theorem eg_eq {i : Nat} (hi : i < 2) : ruEGArr i = unpack 4060 12 (Q7305E.F i) := by
  rw [ruEGArr, Q7305E.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound Q7305E.all i hi


theorem elab_get {y : Nat} (hy : y < 4060) : ruELab[y]! = ELf y := by
  have hs : ruEGArrs.size = 2 := by simp [ruEGArrs]
  have hg : ∀ k < 2, ∀ x < 4060, ga ruEGArrs k x = gE k x := fun k hk x hx => by
    unfold ga ruEGArrs
    rw [getElem!_ofFn_of_lt _ hk]
    change (ruEGArr k)[x]! = _
    rw [eg_eq hk, CFSG.KC.BfsPin.unpack_get' hx]
    rfl
  exact (orbLabels_of_K hs hg kOrbE).2 y hy

theorem elab_lt {y : Nat} (hy : y < 4060) : ELf y < 9 := by
  have := allN_spec kLt y hy
  simpa using this

theorem tig0_eq : ruTIG0 = unpack 4060 12 TG := by
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
  have hw : ∀ l ∈ Iso7047.twK 32 2808, l ≠ 0 ∧ l.natAbs ≤ 2 := fun l hl => by
    have := List.all_eq_true.1 kWordG l hl
    simpa using this
  have e : ruTreeWord 2808 = Iso7047.twK 32 2808 := Iso7047.treeWordAux_eq 32 2808 (by norm_num)
  obtain ⟨h1, h2⟩ := wordA_eq (S := ruGensA) (k := 2) (by simp [ruGensA]) hS hP _ hw
  change invCand 4060 (wordA 4060 ruGensA ruGensInvA (ruTreeWord 2808)) = _
  rw [hinv, e, h1, inv_eq h2]
  rfl


theorem inS_eq {x : Nat} (hx : x < 4060) : ruInS x = Nat.beq (Lf x) (Lf 2808) := by
  unfold ruInS
  rw [qlab_get hx, show ruG0 = 2808 from rfl, qlab_get (by norm_num), nat_beq]

theorem row_eq {x : Nat} (hx : x < 4060) (ht : fl TG x < 4060) :
    ruRowA ruTIG0 x = Nat.beq (Lf (fl TG x)) (Lf 1) := by
  unfold ruRowA
  rw [tig0_eq, CFSG.KC.BfsPin.unpack_get' hx, qlab_get (by unfold fl at ht; simpa using ht),
    qlab_get (by norm_num), nat_beq]
  rfl


theorem sel_eq {p : Nat → Bool} : ∀ xs : List Nat, (∀ x ∈ xs, x < 4060) →
    xs.countP (fun x => p (ELf x)) =
      ∑ l ∈ Finset.range 9, if p l then xs.countP (fun x => Nat.beq (ELf x) l) else 0
  | [], _ => by simp
  | x :: xs, h => by
    have ih := sel_eq (p := p) xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hlt := elab_lt (h x List.mem_cons_self)
    simp only [List.countP_cons, ih]
    have e1 : ∀ l ∈ Finset.range 9, (if p l then
        (xs.countP (fun x => Nat.beq (ELf x) l) + if Nat.beq (ELf x) l = true then 1 else 0) else 0) =
        (if p l then xs.countP (fun x => Nat.beq (ELf x) l) else 0) +
          (if ELf x = l then (if p l then 1 else 0) else 0) := fun l _ => by
      by_cases hp : p l <;> by_cases he : ELf x = l <;> simp [hp, he, Nat.beq_eq]
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_ite_eq,
      if_pos (Finset.mem_range.2 hlt)]


end CertificateChecks.KernelSporSch.Q7305

end
