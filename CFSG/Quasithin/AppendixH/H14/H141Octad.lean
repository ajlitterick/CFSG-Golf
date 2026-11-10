module

public import Mathlib
public import CFSG.Milestones.ASVolI.H1
public import CFSG.Quasithin.AppendixH.H14.Vocab
public import CFSG.Quasithin.AppendixH.H14.H142Conj
public import CFSG.Quasithin.AppendixH.H14.H142Group
public import CFSG.Quasithin.AppendixH.Common.OctadTwoCore
public import CFSG.Quasithin.AppendixH.Common.OctadCentralizer
public import CFSG.Quasithin.AppendixH.Common.OctadOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore
public import CFSG.Quasithin.Background.H16TwoM22

public section

open scoped Pointwise

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI.ChH CFSG.ASVolI.AppH CFSG.Monster.Code CFSG.Open


theorem exists_mulEquiv_elemAbelian_two {G : Type*} [Group G] [Finite G] (E : Subgroup G)
    (hE : IsElemAbelian 2 E) (n : ℕ) (hcard : Nat.card ↥E = 2 ^ n) :
    Nonempty (↥E ≃* Multiplicative (Fin n → ZMod 2)) := by
  classical
  letI : CommGroup ↥E := @IsMulCommutative.instCommGroup _ _ hE.1
  have hsq : ∀ y : ↥E, y ^ 2 = 1 := fun y => Subtype.ext (hE.2 (y : G) y.2)
  haveI : Module (ZMod 2) (Additive ↥E) :=
    AddCommGroup.zmodModule fun x => by
      apply Additive.toMul.injective
      simpa [toMul_nsmul] using hsq (Additive.toMul x)
  have hcardAdd : Nat.card (Additive ↥E) = 2 ^ n := by
    rw [← hcard]
    exact Nat.card_congr Additive.toMul
  have hfin : Module.finrank (ZMod 2) (Additive ↥E) = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥E)
    rw [Nat.card_zmod, hcardAdd] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  let b : Module.Basis (Fin n) (ZMod 2) (Additive ↥E) :=
    Module.finBasisOfFinrankEq (ZMod 2) (Additive ↥E) hfin
  exact ⟨AddEquiv.toMultiplicativeRight b.equivFun.toAddEquiv⟩


end CFSG.Quasithin.AppendixH.H14
