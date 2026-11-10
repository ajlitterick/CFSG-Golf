module

public import Certificates.Data.Kernel.Spor.WordF
public import CFSG.Certificates.Kernel.Spor.SiftEq
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.StrongOfSound
import CFSG.Certificates.Kernel.U52.EvSound
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.HNOddCore.ChainUtil

public section

namespace CFSG.KS.WordF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb

variable {n w : Nat}

@[expose] def Rng (n w P : Nat) : Prop := ∀ x < n, pg w (mask w) P x < n

@[expose] def Canon (n w P : Nat) : Prop := P >>> (n * w) = 0


theorem rng_pcomp (hn : n < 2 ^ 32) {P Q : Nat} (hP : Rng n w P) (hQ : Rng n w Q) :
    Rng n w (pcomp n w (mask w) P Q) := fun x hx => by
  rw [CFSG.KS.PF.pg_pcomp hn hx]
  exact hP _ (hQ x hx)

theorem canon_pcomp (hn : n < 2 ^ 32) (hw : 0 < w) (P Q : Nat) :
    Canon n w (pcomp n w (mask w) P Q) :=
  CFSG.KS.PF.pcomp_shr P Q hn hw

theorem rng_pidn (hn : n < 16777216) (hw : n + 1 < 2 ^ w) : Rng n w (pidn n w) := fun x hx => by
  rw [CFSG.KS.PF.pg_pidn hn hw hx]
  exact hx

theorem canon_pidn (hn : n < 16777216) (hw : n + 1 < 2 ^ w) : Canon n w (pidn n w) :=
  CFSG.KS.PF.pidn_shr hn hw

theorem rng_of_permOK {P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) : Rng n w P :=
  fun x hx => ((permOK_facts h).2.2 x hx).1

theorem canon_of_permOK {P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) :
    Canon n w P :=
  (permOK_facts h).1

theorem canon_evFK (hn : n < 2 ^ 32) (hn' : n < 16777216) (hw : n + 1 < 2 ^ w) {k : Nat}
    (LP LPI : Nat → Nat) (wd : List (Fin k × Bool)) :
    Canon n w (evFK n w (mask w) (pidn n w) LP LPI wd) := by
  cases wd with
  | nil => exact canon_pidn hn' hw
  | cons l wd => exact canon_pcomp hn (CFSG.KS.PF.w_pos hw) _ _

theorem rng_evFK (hn : n < 2 ^ 32) (hn' : n < 16777216) (hw : n + 1 < 2 ^ w) {k : Nat}
    {LP LPI : Nat → Nat} (hr : ∀ i < k, Rng n w (LP i) ∧ Rng n w (LPI i))
    (wd : List (Fin k × Bool)) : Rng n w (evFK n w (mask w) (pidn n w) LP LPI wd) := by
  induction wd with
  | nil => exact rng_pidn hn' hw
  | cons l wd ih =>
    obtain ⟨⟨i, hi⟩, b⟩ := l
    have e : evFK n w (mask w) (pidn n w) LP LPI ((⟨i, hi⟩, b) :: wd) =
        pcomp n w (mask w) (cond b (LP i) (LPI i)) (evFK n w (mask w) (pidn n w) LP LPI wd) := by
      cases b <;> rfl
    rw [e]
    refine rng_pcomp hn ?_ ih
    cases b
    · exact (hr i hi).2
    · exact (hr i hi).1


theorem canon_getD {α : Type} {f : α → Nat} (hf : ∀ x, Canon n w (f x)) (l : List α) (i : Nat)
    {d : Nat} (hd : Canon n w d) : Canon n w ((l.map f).getD i d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? with
  | none => exact hd
  | some a => exact hf a

theorem rng_getD {α : Type} {f : α → Nat} (hf : ∀ x, Rng n w (f x)) (l : List α) (i : Nat)
    {d : Nat} (hd : Rng n w d) : Rng n w ((l.map f).getD i d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? with
  | none => exact hd
  | some a => exact hf a


end CFSG.KS.WordF

end
