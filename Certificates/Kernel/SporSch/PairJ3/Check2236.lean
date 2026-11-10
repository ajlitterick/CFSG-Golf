
module

public import Certificates.Kernel.SporSch.PairJ3.Tab
public import Certificates.Kernel.SporSch.PairJ3.CertSt
public import Certificates.Kernel.SporSch.PairJ3.GenForms
public import CFSG.Certificates.Kernel.SporSch.PairKSound
public import CFSG.Certificates.Kernel.SporSch.J4STokSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_le70 CertificateChecks.KernelSporSch.PJ3F CFSG.Sporadic.Schreier.j3InvHex

namespace CertificateChecks.KernelSporSch.PJ3Cert

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairF2 CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSporSch

theorem andT {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]
  rfl

theorem with_of (bytes : ByteArray) (S : Array (Array Nat))
    (R : List (List Nat) × List (Nat × List (Nat × Nat × Nat))) (hR : j3StabData = R)
    (h1 : ((monomials 80).length == 3240) = true)
    (h2 : (List.range 80).all (fun i => (List.range 80).all fun j =>
      !decide (i ≤ j) || (monomials 80)[pairIdx 80 i j]? == some (i, j)) = true)
    (h3 : allLt 6156 (fun r => decide (hexAt bytes (810 * r) 810 < 2 ^ 3240)) = true)
    (h4 : decide (j3InvWord < 2 ^ 3240) = true) (h5 : (S.size == 5) = true)
    (h6 : allLt 5 (fun j => S[j]!.size == 6156 && isInvA 6156 S[j]! (rawInvs 6156 S)[j]!) = true)
    (h7 : (R.1.length == 8) = true)
    (h8 : R.1.all (fun o => PairNative.strictInc o && o.all (· < 6156)) = true)
    (h9 : (R.1.map List.length == [1, 1360, 2040, 1360, 510, 680, 120, 85]) = true)
    (h10 : (R.2.map Prod.fst == [1, 4, 7, 8, 26, 47, 205]) = true)
    (h11 : (R.2.map (fun m => m.2.length) == [6154, 6154, 6154, 6154, 6154, 6154, 6154]) = true)
    (h12 : R.2.all (fun m => m.2.all fun t => decide (t.1 < 2) && decide (t.2.1 < 6156) &&
      decide (t.2.2 < 6156)) = true) :
    j3CertOKWith bytes S = true := by
  unfold j3CertOKWith j3Monomials
  rewrite [j3StabOrbits_def, j3Merges_def, hR]
  exact andT (andT (andT (andT (andT (andT (andT (andT (andT (andT (andT h1 h2) h3) h4) h5) h6)
    h7) h8) h9) h10) h11) h12

theorem arr_eq (j : Nat) (hj : j < 5) : j3StrongArrs[j]! = unpack 6156 13 (PJ3.S j) := by
  have h := hexTabK_sound PJ3Check.tab j hj
  rewrite [← PJ3Text.eq] at h
  rewrite [j3StrongArrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact h

theorem inv_eq (l : Nat) (hl : l < 5) :
    (rawInvs 6156 j3StrongArrs)[l]! = unpack 6156 13 (PJ3.SI l) := by
  have hI := (invEqK_sound (allN_spec PJ3Check.perm l hl)).1
  have hsz : j3StrongArrs.size = 5 := by simp [j3StrongArrs]
  rewrite [← hI, ← arr_eq l hl, rawInvs, getElem!_pos (j3StrongArrs.map (invCand 6156)) l
    (by simp [hsz]; omega), getElem!_pos j3StrongArrs l (by omega), Array.getElem_map]
  rfl

theorem gens_ok : allLt 5 (fun j => j3StrongArrs[j]!.size == 6156 &&
    isInvA 6156 j3StrongArrs[j]! (rawInvs 6156 j3StrongArrs)[j]!) = true := by
  rewrite [allLt_iff]
  intro j hj
  rewrite [inv_eq j hj, arr_eq j hj, (invEqK_sound (allN_spec PJ3Check.perm j hj)).2]
  simp [unpack]


theorem stab_eq : j3StabData = PJ3St.R := by
  rewrite [j3StabData, PJ3St.eq, tokK_sound PJ3Cert.tok, PJ3Enc.parse_encOM]
  rfl


end CertificateChecks.KernelSporSch.PJ3Cert

end
