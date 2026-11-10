module

public import CFSG.Monster.Existence.TwoPoint.HNRigid
public import CFSG.Monster.Existence.TwoPoint.Fi23Data
public import CFSG.Monster.Existence.TwoPoint.ThreeRepsDefs
public import Certificates.Data.CFSGNative.Bridge.Fi23GPL

public section

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B.Short
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

@[expose] def fiRelW (R : List (ℕ × Bool)) : List Native.Gen :=
  (R.reverse.map fun l => fiWU[l.1]!).flatten


@[expose] def fiNotTau : Native.Gen → Bool
  | .tau => false
  | _ => true

theorem fiNotTau_spec {g : Native.Gen} (h : fiNotTau g = true) : ¬ g = .tau := by
  cases g <;> simp_all [fiNotTau]


@[expose] def fiWAB : List Native.Gen := fiWBeta ++ fiWAlpha


theorem fiConjCheck_parts
    (h : wordLin (fiRhoT ++ fiCAlpha) = wordLin (fiCAlpha ++ fiWAlpha) ∧
      wordLin (fiWAB ++ fiCThreeA) = wordLin (fiCThreeA ++ wordThreeA)) :
    wordLin fiCAlpha * wordLin fiRhoT = wordLin fiWAlpha * wordLin fiCAlpha ∧
      wordLin fiCThreeA * wordLin fiWAB = wordLin wordThreeA * wordLin fiCThreeA := by
  obtain ⟨h1, h2⟩ := h
  rw [wordLin_append, wordLin_append] at h1 h2
  exact ⟨h1, h2⟩

end CFSG.Monster.Existence
