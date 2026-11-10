module

public import Certificates.Data.Kernel.Spor.FpBfs
public import CFSG.Sporadic.SuzRecog.LevelTwoCheck
public import CFSG.Certificates.Kernel.Spor.KeyBfsGen
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

namespace CFSG.KS.FpBfs

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.SuzRecog.LevelTwo


theorem compA_get {t u : Array Nat} {x : Nat} (hx : x < 1782) :
    (compA 1782 t u)[x]! = t[u[x]!]! := by
  rw [compA, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem fpConj_eq (g gi a : Array Nat) : fpConj g gi a = fp (conjA g gi a) := by
  unfold fp fpConj conjA
  simp only [compA_get (by norm_num : (17 : Nat) < 1782), compA_get (by norm_num : (333 : Nat) < 1782),
    compA_get (by norm_num : (901 : Nat) < 1782), compA_get (by norm_num : (1500 : Nat) < 1782),
    compA_get (by norm_num : (1234 : Nat) < 1782), compA_get (by norm_num : (77 : Nat) < 1782)]

theorem unpack_get {p i : Nat} (hi : i < 1782) : (unpack 1782 11 p)[i]! = pg 11 (mask 11) p i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem canon_lt {p i : Nat} (hp : CFSG.KS.Prim.canonK 1782 11 (mask 11) (1782 * 11) p = true)
    (hi : i < 1782) : pg 11 (mask 11) p i < 1782 := by
  unfold CFSG.KS.Prim.canonK at hp
  simp only [bAnd_iff] at hp
  simpa [Nat.blt_eq] using allN_spec hp.2.2 i hi


theorem fpConj_unpack {G GI T : Nat} (hgi : ∀ i < 1782, pg 11 (mask 11) GI i < 1782)
    (ht : ∀ i < 1782, pg 11 (mask 11) T i < 1782) :
    fpConj (unpack 1782 11 G) (unpack 1782 11 GI) (unpack 1782 11 T) = fpCK 11 (mask 11) G GI T := by
  have e : ∀ i < 1782, (unpack 1782 11 G)[(unpack 1782 11 T)[(unpack 1782 11 GI)[i]!]!]! =
      pg 11 (mask 11) G (pg 11 (mask 11) T (pg 11 (mask 11) GI i)) := fun i hi => by
    rw [unpack_get hi, unpack_get (hgi i hi), unpack_get (ht _ (hgi i hi))]
  unfold fpConj fpCK fpOf
  simp only []
  rw [e 17 (by norm_num), e 333 (by norm_num), e 901 (by norm_num), e 1500 (by norm_num),
    e 1234 (by norm_num), e 77 (by norm_num)]
  rfl

theorem fp_unpack (T : Nat) : fp (unpack 1782 11 T) = fpK 11 (mask 11) T := by
  have g : ∀ i < 1782, (unpack 1782 11 T)[i]! = pg 11 (mask 11) T i := fun i hi => by
    rw [getElem!_pos (unpack 1782 11 T) i (by simp [unpack, hi])]
    simp [unpack]
  unfold fp
  rw [g 17 (by norm_num), g 333 (by norm_num), g 901 (by norm_num), g 1500 (by norm_num),
    g 1234 (by norm_num), g 77 (by norm_num)]
  rfl

theorem blt_true {a b : Nat} (h : Nat.blt a b = true) : a < b := by simpa [Nat.blt_eq] using h


end CFSG.KS.FpBfs

end
