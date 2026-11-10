
module

public import CFSG.Sporadic.Th.TableSpec
public import CFSG.Sporadic.Th.F2Spec

@[expose] public section

namespace CFSG.Sporadic.Th

open Native Matrix Pointwise

abbrev V := Fin 248 → ZMod 2

noncomputable abbrev W : Set V := keyPlane wKey

noncomputable abbrev thSt : BFSState := thBFS ()

noncomputable abbrev nX : ℕ := thSt.count

noncomputable abbrev planeAt (i : ℕ) : Set V := keyPlane (readKey thSt.keys i)

noncomputable abbrev αIdx (i : ℕ) : ℕ := readU32 thSt.alpha i

noncomputable abbrev βIdx (i : ℕ) : ℕ := readU32 thSt.beta i

noncomputable abbrev parIdx (i : ℕ) : ℕ := treePar (readU32 thSt.par i)

noncomputable abbrev labIdx (i : ℕ) : ℕ := treeLab (readU32 thSt.par i)

structure OrbitFacts : Prop where
  pos : 0 < nX
  lt : nX < 2 ^ 30
  root : readKey thSt.keys 0 = wKey
  canonical : ∀ i < nX, (readKey thSt.keys i).isCanonical = true
  slot : ∀ i < nX, (findSlot thSt.keys thSt.slots (readKey thSt.keys i)).2 = i + 1
  αlt : ∀ i < nX, αIdx i < nX
  βlt : ∀ i < nX, βIdx i < nX
  αkey : ∀ i < nX, readKey thSt.keys (αIdx i) = imageKey (tblA ()) (readKey thSt.keys i)
  βkey : ∀ i < nX, readKey thSt.keys (βIdx i) = imageKey (tblB ()) (readKey thSt.keys i)
  tree : ∀ i < nX, 0 < i → parIdx i < i ∧
    ((labIdx i = 1 ∧ αIdx (parIdx i) = i) ∨ (labIdx i = 2 ∧ βIdx (parIdx i) = i))


section Facts

variable (hF : OrbitFacts)
include hF

theorem planeAt_injective : ∀ i < nX, ∀ j < nX, planeAt i = planeAt j → i = j := by
  intro i hi j hj h
  have hk := eq_of_keyPlane_eq (hF.canonical i hi) (hF.canonical j hj) h
  have := hF.slot i hi
  rw [hk, hF.slot j hj] at this
  omega

theorem planeAt_zero : planeAt 0 = W := by
  rw [planeAt, hF.root]

end Facts

end CFSG.Sporadic.Th
