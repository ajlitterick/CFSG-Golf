module

public import CFSG.Monster.AxisCount.HSIdentAxis
public import CFSG.Monster.AxisCount.BabyData

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount.Baby

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.B CFSG.Monster.B.Short
open CFSG.Monster.AxisCount.HS (axisP axisM hsCtx eqCheck eqCheck_sound interp_axisP interp_axisM
  isTauB mem_bool)

@[expose] def bo : Nat → BabyOrbit
  | 0 => babyOrbit0
  | 1 => babyOrbit1
  | 2 => babyOrbit2
  | 3 => babyOrbit3
  | 4 => babyOrbit4
  | 5 => babyOrbit5
  | 6 => babyOrbit6
  | 7 => babyOrbit7
  | 8 => babyOrbit8
  | 9 => babyOrbit9
  | _ => default

@[expose] def nrec (j : Nat) : Nat := (bo j).h.size

@[expose] def gW (j : Nat) : List Native.Gen := segsWord (bo j).gamma

@[expose] def hW (j r : Nat) : List Native.Gen := (bo j).h[r]!

@[expose] def kW (j r : Nat) : Bool → List Native.Gen
  | true => (bo j).kappaPlus[r]!
  | false => (bo j).kappaMinus[r]!

@[expose] def tgt (j r : Nat) : Bool → Nat
  | true => (bo j).tPlus[r]!
  | false => (bo j).tMinus[r]!

@[expose] def sz (j r : Nat) : Nat := (bo j).size[r]!

@[expose] def tpw : Bool → List Native.Gen
  | true => [Native.Gen.tau]
  | false => Native.Gen.tauPow 2

@[expose] def xW (j r : Nat) (ε : Bool) : List Native.Gen := hW j r ++ tpw ε ++ kW j r ε

@[expose] noncomputable def vv (j : Nat) : SpaceB := wordLin (gW j) aStarMinus

@[expose] def vtab : Array Native.DVec :=
  ((List.range 10).map fun j => Native.evalWordC hsCtx (gW j) axisM).toArray

@[expose] def vtabOK : Bool := (List.range 10).all fun j => (gW j).all Native.Gen.validB


@[expose] def jWords (j : Nat) : List (List Native.Gen) :=
  (bo j).U ++ (bo j).h.toList ++ (bo j).kappaPlus.toList ++ (bo j).kappaMinus.toList

@[expose] def fixOK (j : Nat) : Bool :=
  (jWords j).all fun w => w.all (fun g => !isTauB g) && eqCheck hsCtx w axisP [] axisP

theorem fixOK_sound {j : Nat} (h : fixOK j = true) :
    ∀ w ∈ jWords j, (∀ g ∈ w, g ≠ Native.Gen.tau) ∧ wordLin w aStar = aStar := by
  intro w hw
  have h1 := List.all_eq_true.1 h w hw
  rw [Bool.and_eq_true] at h1
  refine ⟨fun g hg e => ?_, ?_⟩
  · have := List.all_eq_true.1 h1.1 g hg
    subst e
    simp [isTauB] at this
  · have := eqCheck_sound h1.2
    rw [interp_axisP] at this
    simpa [wordLin_nil] using this

@[expose] def segOK : Seg → Bool
  | .blk w => w.all (fun g => !isTauB g) && eqCheck hsCtx w axisP [] axisP
  | .tau _ => true

@[expose] def gammaOK (j : Nat) : Bool := (bo j).gamma.all segOK


@[expose] def OrbitIdent (j : Nat) : Prop :=
  (∀ w ∈ (bo j).U, wordLin w (vv j) = vv j) ∧
    (∀ r, r < nrec j → ∀ ε, tgt j r ε < 10 ∧ wordLin (xW j r ε) (vv j) = vv (tgt j r ε)) ∧
    (∀ w ∈ jWords j, (∀ g ∈ w, g ≠ Native.Gen.tau) ∧ wordLin w aStar = aStar) ∧
    (∀ w, Seg.blk w ∈ (bo j).gamma → (∀ g ∈ w, g ≠ Native.Gen.tau) ∧ wordLin w aStar = aStar)

end CFSG.Monster.AxisCount.Baby
